#!/usr/bin/env python3
"""Daily re-price for the podcast stock tracker.

Reads index.html (the live site file), re-prices every priced record to the
latest completed trading day, recomputes ret / spy / excess vs SPY, updates
the date strings, and writes index.html back.

Method (matches the manual re-prices to date):
  * Prices come from the StockAnalysis API (daily closes, unadjusted) for
    SPY and every US-listed ticker. The Yahoo Finance chart API is used
    only for the tickers StockAnalysis does not cover (foreign listings,
    plus the US-listed NTDOY and OTCM) — Yahoo rate-limits GitHub's
    shared runner IPs, so it must never be the primary source.
  * Entry prices, classifications and entry dates NEVER change.
  * ret  = (last / entry - 1) * 100
  * The file stores no SPY entry price per record, so the SPY entry close is
    recovered from the stored spy return and the SPY close on the file's
    current as-of date:  spy_entry = as_of_spy_close / (1 + stored_spy/100).
    This preserves special cases (e.g. EQT, whose SPY entry is the 20 Jun
    2025 close because 19 Jun was Juneteenth). New spy return is then
    (new_spy_close / spy_entry - 1) * 100.
  * excess = unrounded ret minus unrounded spy; all values rounded to 2dp
    (Decimal, round-half-up). Foreign rows are priced in their listing
    currency, FX-unadjusted vs USD SPY.
  * Cross-check: every ticker's close on the as-of date (or latest close on
    or before it) must match the file's stored `last` value. Any mismatch
    means a wrong symbol or bad data, so the run fails loudly and writes
    nothing.
  * WBD is held at $30.95 (ceased trading after the 5 Oct 2026 close; no
    later close exists) and is never re-priced.
  * MSGS is tracked as a combined holding: 1 MSGK + 0.5 x MSGR.
  * Records with no `last` value (no ticker, exits with no prices, the
    Melvin preferreds, GMWKF, EVO x2, LMN) are left unchanged.
  * Idempotent: a second run for the same close changes nothing and exits 0
    with "already current". If the latest SPY close is the as-of date (e.g.
    a market holiday, or Yahoo has not published the close yet) nothing is
    written.
  * A StockAnalysis fetch failure (after retries) or a cross-check
    mismatch is a fatal error: the script prints the problem and exits
    non-zero WITHOUT writing the file, so the workflow fails loudly
    instead of writing bad data. A Yahoo fetch failure is NOT fatal:
    the affected record is left unchanged and a warning is logged, so
    Yahoo rate-limiting can never fail the run.

Usage:
  python3 scripts/reprice.py [--file path/to/index.html]
  (default file is index.html next to the scripts/ directory, i.e. the repo
  root). When GITHUB_OUTPUT is set (GitHub Actions), writes
  target_date / spy_close / records_repriced there for the workflow to use
  in its commit message.
"""

import argparse
import json
import os
import re
import sys
import time
import urllib.error
import urllib.request
from datetime import datetime, timezone
from decimal import ROUND_HALF_UP, Decimal

# ---------------------------------------------------------------- constants

STOCKANALYSIS_HISTORY = ("https://api.stockanalysis.com/api/symbol/s/{sym}"
                         "/history?range=3mo&period=Daily")
YAHOO_CHART = "https://query1.finance.yahoo.com/v8/finance/chart/{sym}?range=3mo&interval=1d"
USER_AGENT = (
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/120.0 Safari/537.36"
)
SPY_SYMBOL = "SPY"

# Tickers StockAnalysis does not cover, so they are priced from Yahoo.
# Determined 19 Nov 2026 by testing every priced ticker in index.html
# against the StockAnalysis API: 109 of 128 matched, and these 17 did
# not. 15 are foreign listings; NTDOY (Nintendo ADR) and OTCM (OTC
# Markets Group) are US-listed but StockAnalysis has no data for them.
# Yahoo failures for these tickers are tolerated (see series_for).
YAHOO_TICKERS = {
    "121440.KQ",  # Korea (KOSDAQ)
    "ADYEN",      # Adyen, Amsterdam
    "CPG.L",      # Compass Group, London
    "EQT.ST",     # EQT, Stockholm
    "EXO",        # Exor (TIP836 row); plain "EXO" returns no Yahoo data
    "EXO.AS",     # Exor, Amsterdam
    "FOUR.L",     # 4imprint, London
    "HWDN",       # Howden Joinery, London
    "INF.L",      # Informa, London
    "ITX.MC",     # Inditex, Madrid
    "KER.PA",     # Kering, Paris
    "MC.PA",      # LVMH, Paris
    "NTDOY",      # Nintendo ADR (US-listed, no StockAnalysis data)
    "OTCM",       # OTC Markets Group (US-listed, no StockAnalysis data)
    "RMS.PA",     # Hermes, Paris
    "UHR",        # Swatch, Zurich
    "WISE.L",     # Wise, London
}

# File ticker -> Yahoo symbol, for the bare foreign tickers (the dotted
# ones are already Yahoo symbols and are used as-is). StockAnalysis takes
# the file's own spelling, including the dot in class shares (BRK.B,
# HEI.A), so no mapping is needed for it.
YAHOO_SYMBOL_MAP = {
    "HWDN": "HWDN.L",
    "UHR": "UHR.SW",
    "ADYEN": "ADYEN.AS",
    "EXO": "EXO.AS",
}

# Never re-price: WBD ceased trading after the 5 Oct 2026 close.
HELD_TICKERS = {"WBD"}

# A ticker whose latest close is more than this many calendar days before the
# target date is treated as stale data and fails the run.
MAX_STALE_DAYS = 10

# Cross-check tolerance for stored `last` vs the source's as-of close: the
# larger of 2 cents or 0.05% of the price.
TOL_ABS = 0.02
TOL_REL = 0.0005

MONTHS = ["Jan", "Feb", "Mar", "Apr", "May", "Jun",
          "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]


def fmt_date(d):
    """'19 Nov 2026' — the format used throughout index.html."""
    return "%d %s %d" % (d.day, MONTHS[d.month - 1], d.year)


def parse_file_date(s):
    return datetime.strptime(s, "%d %b %Y").date()


def r2(x):
    """Round to 2dp, half-up, as a float; -0.00 normalised to 0.00."""
    v = float(Decimal(str(x)).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP))
    return 0.0 if v == 0 else v


# ---------------------------------------------------------------- fetching

class SymbolNotCovered(RuntimeError):
    """StockAnalysis has no data for this symbol (HTTP 400/404)."""


def fetch_stockanalysis(symbol, attempts=5):
    """Daily closes from the StockAnalysis API -> {date: close}. Uses the
    "c" (unadjusted close) field; "a" is the adjusted close and is NOT
    used. Retries with exponential backoff on HTTP 429 / 5xx / network
    errors. A 400/404 means the symbol is not covered, so it raises
    SymbolNotCovered (the caller falls back to Yahoo)."""
    url = STOCKANALYSIS_HISTORY.format(sym=symbol)
    last_err = None
    for attempt in range(attempts):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            with urllib.request.urlopen(req, timeout=25) as resp:
                data = json.load(resp)
            if data.get("status") != 200 or not data.get("data"):
                if data.get("status") in (400, 404):
                    raise SymbolNotCovered(
                        "StockAnalysis has no data for %s (status %s)"
                        % (symbol, data.get("status")))
                raise RuntimeError("StockAnalysis error for %s: status %s"
                                   % (symbol, data.get("status")))
            series = {}
            for row in data["data"]:
                if row.get("c") is None or not row.get("t"):
                    continue
                d = datetime.strptime(row["t"], "%Y-%m-%d").date()
                series[d] = float(row["c"])
            if not series:
                raise SymbolNotCovered(
                    "StockAnalysis returned no closes for %s" % symbol)
            return series
        except urllib.error.HTTPError as exc:
            # 400/404 is "not covered", not transient: do not retry.
            if exc.code in (400, 404):
                raise SymbolNotCovered(
                    "StockAnalysis has no data for %s: HTTP %s"
                    % (symbol, exc.code))
            if exc.code in (401, 403):
                raise RuntimeError("StockAnalysis request failed for %s: HTTP %s"
                                   % (symbol, exc.code))
            last_err = exc
        except (urllib.error.URLError, TimeoutError) as exc:
            last_err = exc
        delay = (2 ** attempt) + (0.5 if attempt % 2 else 0.0)
        print("  retry %s in %.1fs (%s)" % (symbol, delay, last_err),
              file=sys.stderr)
        time.sleep(delay)
    raise RuntimeError("StockAnalysis request failed for %s after %d attempts: %s"
                       % (symbol, attempts, last_err))


def fetch_chart(symbol, attempts=5):
    """Daily closes from Yahoo chart API -> {date: close}. Retries with
    exponential backoff on HTTP 429 / 5xx / network errors."""
    url = YAHOO_CHART.format(sym=symbol)
    last_err = None
    for attempt in range(attempts):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            with urllib.request.urlopen(req, timeout=25) as resp:
                data = json.load(resp)
            result = data.get("chart", {}).get("result")
            if not result:
                err = data.get("chart", {}).get("error") or "no result"
                raise ValueError("Yahoo returned no data for %s: %s" % (symbol, err))
            res = result[0]
            stamps = res.get("timestamp") or []
            closes = (res.get("indicators", {}).get("quote", [{}])[0]
                      .get("close") or [])
            series = {}
            for ts, close in zip(stamps, closes):
                if close is None:
                    continue
                d = datetime.fromtimestamp(ts, timezone.utc).date()
                series[d] = float(close)
            if not series:
                raise ValueError("Yahoo returned no closes for %s" % symbol)
            return series
        except urllib.error.HTTPError as exc:
            # 4xx is a data error, not transient: fail fast.
            if exc.code in (400, 401, 403, 404):
                raise RuntimeError("Yahoo request failed for %s: HTTP %s"
                                   % (symbol, exc.code))
            last_err = exc
        except (urllib.error.URLError, TimeoutError) as exc:
            last_err = exc
        except ValueError as exc:
            raise RuntimeError(str(exc))
        delay = (2 ** attempt) + (0.5 if attempt % 2 else 0.0)
        print("  retry %s in %.1fs (%s)" % (symbol, delay, last_err),
              file=sys.stderr)
        time.sleep(delay)
    raise RuntimeError("Yahoo request failed for %s after %d attempts: %s"
                       % (symbol, attempts, last_err))


def close_on_or_before(series, target):
    """Latest close on or before `target` -> (date, close) or (None, None)."""
    best = None
    for d in sorted(series):
        if d <= target:
            best = d
        else:
            break
    return (best, series[best]) if best is not None else (None, None)


# ---------------------------------------------------------------- parsing

def split_records(picks_text):
    """Split the PICKS array body into top-level {...} objects, respecting
    double-quoted strings and escapes. Returns a list of (start, end, text)
    so the interstitial text (comments, commas, whitespace) is preserved
    when the objects are spliced back in."""
    spans, i, n = [], 0, len(picks_text)
    while i < n:
        if picks_text[i] == "{":
            depth, j, in_str, esc = 1, i + 1, False, False
            while j < n and depth:
                c = picks_text[j]
                if in_str:
                    if esc:
                        esc = False
                    elif c == "\\":
                        esc = True
                    elif c == '"':
                        in_str = False
                else:
                    if c == '"':
                        in_str = True
                    elif c == "{":
                        depth += 1
                    elif c == "}":
                        depth -= 1
                j += 1
            spans.append((i, j, picks_text[i:j]))
            i = j
        else:
            i += 1
    return spans


NUM_FIELD = r",%s:(-?[\d.]+)"


def split_head(obj):
    """Split a record object into (head, tail) at the `,quote:` field, so
    field edits never touch a quote or note string."""
    parts = obj.split(",quote:", 1)
    if len(parts) == 2:
        return parts[0], ",quote:" + parts[1]
    return obj, ""


def record_fields(obj):
    """Extract the pricing fields from one record object (head only)."""
    head, _ = split_head(obj)
    tick_m = re.search(r'ticker:"((?:[^"\\]|\\.)*)"', head)
    out = {"ticker": tick_m.group(1) if tick_m else None}
    for name in ("entry", "last", "ret", "spy", "excess"):
        m = re.search(NUM_FIELD % name, head)
        out[name] = float(m.group(1)) if m else None
    return out


def replace_fields(obj, values):
    """Replace numeric fields in a record object (head only), formatting to
    2dp, then verify by re-parsing. `values` maps field name -> new value."""
    head, tail = split_head(obj)
    for name, value in values.items():
        new_head, n = re.subn(NUM_FIELD % name, ",%s:%.2f" % (name, value),
                              head, count=1)
        if n != 1:
            raise RuntimeError("could not replace field %s in record: %s"
                               % (name, obj[:120]))
        head = new_head
    new_obj = head + tail
    check = record_fields(new_obj)
    for name, value in values.items():
        if check[name] != value:
            raise RuntimeError("field %s did not update as expected in %s"
                               % (name, obj[:80]))
    return new_obj


# ---------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser(description="Daily re-price for the podcast stock tracker.")
    ap.add_argument("--file", default=None,
                    help="path to index.html (default: index.html next to scripts/)")
    args = ap.parse_args()

    if args.file:
        index_path = args.file
    else:
        here = os.path.dirname(os.path.abspath(__file__))
        index_path = os.path.join(os.path.dirname(here), "index.html")

    with open(index_path, encoding="utf-8") as fh:
        html = fh.read()

    # --- current as-of date, from the KPI box ---------------------------
    kpi = re.search(
        r'<div class="kpi"><div class="n">(\d{1,2} [A-Z][a-z]{2} \d{4})</div>'
        r'<div class="l">prices current to the last completed trading day</div>',
        html)
    if not kpi:
        sys.exit("ERROR: could not find the as-of date KPI in index.html")
    as_of_str = kpi.group(1)
    as_of = parse_file_date(as_of_str)
    print("file as-of date: %s" % as_of_str)

    # --- SPY: as-of close and latest close -------------------------------
    print("fetching SPY ...")
    spy_series = fetch_stockanalysis(SPY_SYMBOL)
    as_of_spy_date, as_of_spy = close_on_or_before(spy_series, as_of)
    if as_of_spy_date != as_of:
        sys.exit("ERROR: no SPY close on the as-of date %s (latest on/before: %s)"
                 % (as_of_str, as_of_spy_date))
    target = max(spy_series)
    target_spy = r2(spy_series[target])
    # Round the SPY closes to 2dp first: the API can return extra
    # precision (e.g. 24.703), and the 2dp values are the true closes.
    as_of_spy = r2(as_of_spy)
    target_str = fmt_date(target)
    print("SPY as-of close %s: %.2f ; latest close %s: %.2f"
          % (as_of_str, as_of_spy, target_str, target_spy))
    if target == as_of:
        print("already current to %s; nothing to do." % target_str)
        return 0

    # --- parse the PICKS array -------------------------------------------
    m = re.search(r"var PICKS = \[(.*?)\n\];", html, re.S)
    if not m:
        sys.exit("ERROR: could not find the PICKS array in index.html")
    picks_text = m.group(1)
    spans = split_records(picks_text)
    print("records: %d" % len(spans))

    errors = []
    warnings = []
    repriced = 0
    skipped_no_price = 0
    skipped_held = 0
    skipped_foreign = 0
    new_texts = []

    sa_cache = {}
    yh_cache = {}

    def get_sa_series(symbol):
        if symbol not in sa_cache:
            sa_cache[symbol] = fetch_stockanalysis(symbol)
            time.sleep(0.15)  # be polite between requests
        return sa_cache[symbol]

    def get_yahoo_series(symbol):
        if symbol not in yh_cache:
            yh_cache[symbol] = fetch_chart(symbol)
            time.sleep(0.15)  # be polite to Yahoo between symbols
        return yh_cache[symbol]

    def series_for(ticker):
        """Closes for one file ticker -> {date: close}, or None to leave
        the record unchanged. StockAnalysis is primary; Yahoo is used
        only for the tickers it does not cover (YAHOO_TICKERS) or when
        StockAnalysis says a symbol is not covered. A Yahoo failure only
        skips the record (with a warning) — it never fails the run.
        Raises RuntimeError only when StockAnalysis fails for a ticker
        it is supposed to cover."""
        if ticker in YAHOO_TICKERS:
            sym = YAHOO_SYMBOL_MAP.get(ticker, ticker)
            try:
                return get_yahoo_series(sym)
            except RuntimeError as exc:
                warnings.append("%s: Yahoo fetch failed (%s) — leaving unchanged"
                                % (ticker, exc))
                return None
        try:
            return get_sa_series(ticker)
        except SymbolNotCovered:
            sym = YAHOO_SYMBOL_MAP.get(ticker, ticker)
            try:
                return get_yahoo_series(sym)
            except RuntimeError as exc:
                warnings.append("%s: not covered by StockAnalysis and Yahoo fetch "
                                "failed (%s) — leaving unchanged" % (ticker, exc))
                return None

    for (_s, _e, obj) in spans:
        f = record_fields(obj)
        ticker = f["ticker"]
        # No-price rows: no ticker, an em-dash ticker, or no `last` value.
        if (not ticker or ticker in ("\\u2014", "—") or f["last"] is None):
            skipped_no_price += 1
            new_texts.append(obj)
            continue
        if ticker in HELD_TICKERS:
            skipped_held += 1
            new_texts.append(obj)
            continue
        if f["entry"] is None or f["spy"] is None:
            errors.append("%s: priced record is missing entry/spy" % ticker)
            new_texts.append(obj)
            continue

        # --- fetch the ticker's closes -----------------------------------
        if ticker == "MSGS":
            try:
                msgk = series_for("MSGK")
                msgr = series_for("MSGR")
            except RuntimeError as exc:
                errors.append("MSGS: %s" % exc)
                new_texts.append(obj)
                continue
            if msgk is None or msgr is None:
                # series_for already logged the warning.
                skipped_foreign += 1
                new_texts.append(obj)
                continue

            def combined(series_date):
                d1, c1 = close_on_or_before(msgk, series_date)
                d2, c2 = close_on_or_before(msgr, series_date)
                if d1 is None or d2 is None:
                    return None, None
                return min(d1, d2), r2(c1 + 0.5 * c2)

            as_of_d, as_of_last = combined(as_of)
            tgt_d, new_last = combined(target)
            stale = (target - tgt_d).days if tgt_d else None
        else:
            try:
                series = series_for(ticker)
            except RuntimeError as exc:
                errors.append("%s: %s" % (ticker, exc))
                new_texts.append(obj)
                continue
            if series is None:
                # series_for already logged the warning.
                skipped_foreign += 1
                new_texts.append(obj)
                continue
            as_of_d, as_of_last = close_on_or_before(series, as_of)
            tgt_d, new_last = close_on_or_before(series, target)
            stale = (target - tgt_d).days if tgt_d else None

        # Round closes to 2dp now: the sources can return extra precision
        # (e.g. 24.703) and the file stores 2dp values. Rounding here
        # keeps the cross-check, the stored `last`, and the return maths all
        # consistent with the 2dp values in the file.
        if as_of_last is not None:
            as_of_last = r2(as_of_last)
        if new_last is not None:
            new_last = r2(new_last)

        # --- cross-check against the stored `last` -----------------------
        if as_of_last is None:
            errors.append("%s: no close on or before as-of %s"
                          % (ticker, as_of_str))
            new_texts.append(obj)
            continue
        tol = max(TOL_ABS, TOL_REL * abs(f["last"]))
        if abs(as_of_last - f["last"]) > tol:
            errors.append(
                "%s: cross-check failed — stored last %.2f but close "
                "on %s is %.2f"
                % (ticker, f["last"], as_of_d, as_of_last))
            new_texts.append(obj)
            continue

        # --- new close ----------------------------------------------------
        if new_last is None or stale is None or stale > MAX_STALE_DAYS:
            errors.append("%s: no usable close near target %s (latest %s)"
                          % (ticker, target_str, tgt_d))
            new_texts.append(obj)
            continue
        if stale:
            warnings.append("%s: latest close is %s (%d day(s) before target %s)"
                            % (ticker, tgt_d, stale, target_str))

        # --- recompute returns --------------------------------------------
        unrounded_ret = (new_last / f["entry"] - 1.0) * 100.0
        spy_entry = as_of_spy / (1.0 + f["spy"] / 100.0)
        unrounded_spy = (target_spy / spy_entry - 1.0) * 100.0
        try:
            obj = replace_fields(obj, {
                "last": new_last,
                "ret": r2(unrounded_ret),
                "spy": r2(unrounded_spy),
                "excess": r2(unrounded_ret - unrounded_spy),
            })
        except RuntimeError as exc:
            errors.append("%s: %s" % (ticker, exc))
            new_texts.append(obj)
            continue
        new_texts.append(obj)
        repriced += 1

    if errors:
        print("ERRORS — refusing to write index.html:", file=sys.stderr)
        for e in errors:
            print("  - " + e, file=sys.stderr)
        return 1

    # --- rebuild the PICKS body, splicing objects back in place -----------
    # (interstitial text — section comments, commas, whitespace — is kept
    # exactly as it was).
    parts, pos = [], 0
    for (start, end, _old), new_obj in zip(spans, new_texts):
        parts.append(picks_text[pos:start])
        parts.append(new_obj)
        pos = end
    parts.append(picks_text[pos:])
    new_body = "".join(parts)
    new_html = html[:m.start(1)] + new_body + html[m.end(1):]

    # --- update the date strings (targeted locations only) ----------------
    # KPI box
    new_html, n1 = re.subn(
        r'(<div class="kpi"><div class="n">)' + re.escape(as_of_str) +
        r'(</div><div class="l">prices current to the last completed trading day</div>)',
        r"\g<1>" + target_str + r"\g<2>", new_html)
    # Methodology paragraph
    new_html, n2 = re.subn(
        r"currently the " + re.escape(as_of_str) + r" close",
        "currently the " + target_str + " close", new_html)
    # Mobile-card fallback in the render code
    new_html, n3 = re.subn(
        r'\(p\.lastDate\|\|"' + re.escape(as_of_str) + r'"\)',
        '(p.lastDate||"' + target_str + '")', new_html)
    # Section comments inside the PICKS array ("to 18 Nov 2026",
    # "priced to 18 Nov 2026 close"): replace the date only inside
    # /* ... */ comment spans, so an epDate/entryDate can never be touched.
    comment_hits = []

    def _comment_sub(match):
        span = match.group(0)
        if as_of_str in span:
            comment_hits.append(span)
            return span.replace(as_of_str, target_str)
        return span

    new_html, _n4 = re.subn(r"/\*[^*]*\*/", _comment_sub, new_html)
    if n1 != 1 or n2 != 1 or n3 != 1 or not comment_hits:
        sys.exit("ERROR: date-string update hit an unexpected count "
                 "(KPI=%d methodology=%d fallback=%d comment spans with date=%d)"
                 % (n1, n2, n3, len(comment_hits)))
    print("date strings updated: KPI, methodology, fallback, %d comment span(s)"
          % len(comment_hits))

    if new_html == html:
        print("no changes to write (already current).")
        return 0
    with open(index_path, "w", encoding="utf-8") as fh:
        fh.write(new_html)

    print("re-priced %d records to %s (SPY %.2f); skipped %d no-price, %d held, %d Yahoo-unavailable"
          % (repriced, target_str, target_spy, skipped_no_price, skipped_held,
             skipped_foreign))
    for w in warnings:
        print("  warning: " + w)
    gh_out = os.environ.get("GITHUB_OUTPUT")
    if gh_out:
        with open(gh_out, "a", encoding="utf-8") as fh:
            fh.write("target_date=%s\n" % target_str)
            fh.write("spy_close=%.2f\n" % target_spy)
            fh.write("records_repriced=%d\n" % repriced)
    return 0


if __name__ == "__main__":
    sys.exit(main())
