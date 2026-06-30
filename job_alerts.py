"""
Job Alert Bot + Live Portal - RBCET CSE/AI Placement Cell  (v2)

Each run it:
  1. Searches Google News for the queries in queries.txt (categorised).
  2. Posts ONLY NEW items to the Telegram channel (push layer).
  3. Updates jobs.json and regenerates docs/index.html - a segmented,
     searchable portal served free by GitHub Pages (browse layer).

Env vars (GitHub repo Secrets):
  TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_ID      Optional: DRY_RUN=1
"""

import hashlib
import html
import json
import os
import re
import sys
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone

SEEN_FILE = "seen.json"
JOBS_FILE = "jobs.json"
PORTAL_FILE = os.path.join("docs", "index.html")
QUERIES_FILE = "queries.txt"
SOURCES_FILE = "sources.txt"
TELEGRAM_LINK = "https://t.me/rbcet_placements"  # edit to your channel link

MAX_AGE_DAYS = 15        # ignore news older than this when fetching
KEEP_DAYS = 45          # how long items stay on the portal
MAX_JOBS = 600
MAX_ITEMS_PER_QUERY = 8
MAX_SEEN = 8000
IST = timezone(timedelta(hours=5, minutes=30))
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0 Safari/537.36")


# ---- Relevance filter (editable) ----
# A title must contain at least one INCLUDE word and no EXCLUDE word.
INCLUDE_WORDS = ["off campus", "off-campus", "drive", "hiring", "registration",
                 "register", "recruitment", "recruit", "apply", "application",
                 "vacanc", "opening", "walk-in", "walkin", "internship",
                 "intern", "job", "career", "nqt", "hackathon", "freshers"]
EXCLUDE_WORDS = ["layoff", "laid off", "jobless", "shut down", "shutdown",
                 "shuts", "scam", "fraud", "arrested", "strike", "protest",
                 "report", "trends", "summit", "felicitated", "convocation",
                 "fest", "lose job", "loses job", "salary delay"]


def is_relevant(title):
    t = title.lower()
    if any(w in t for w in EXCLUDE_WORDS):
        return False
    return any(w in t for w in INCLUDE_WORDS)


def norm_title(title):
    return re.sub(r"[^a-z0-9]", "", title.lower())[:70]

CATEGORY_ORDER = ["Official Openings", "Hiring Challenges", "Big Tech & GCC",
                  "Services", "Women-only", "General"]
CATEGORY_COLOR = {"Official Openings": "#2f6f6f", "Services": "#2e6e4e",
                  "Hiring Challenges": "#b3541e", "Big Tech & GCC": "#1f4e79",
                  "Women-only": "#8a3a64", "General": "#5a5247"}

# ---- Filter for official ATS feeds (companies post global/senior roles too) ----
INDIA_HINTS = ["india", "bengaluru", "bangalore", "hyderabad", "pune", "mumbai",
               "delhi", "gurugram", "gurgaon", "noida", "chennai", "kolkata",
               "ahmedabad", "jaipur", "indore"]
# CSE/AI-relevant roles only (drops sales, HR, design, PR, finance, content).
# CSE/AI-relevant roles only (drops sales, HR, design, PR, finance, content).
TECH_WORDS = ["engineer", "developer", "software", "sde", "sdet", "programmer",
              "data scientist", "data analyst", "machine learning", " ml ",
              "ml engineer", "ai engineer", "ai/ml", "devops", "sre",
              "qa ", "quality engineer", "backend", "back end", "frontend",
              "front end", "fullstack", "full stack", "cloud", "security",
              "android", "ios", "mobile developer", "platform engineer",
              "systems engineer", "database", "research scientist",
              "applied scientist", "computer"]
SENIOR_WORDS = ["senior", "sr.", "staff", "principal", "lead ", " lead", "manager",
                "director", "head of", "vp ", "vice president", "architect",
                " ii", " iii", " iv", "l3", "l4", "l5", "experienced",
                "expert", "specialist", " sii", " siii"]
# First-job signals in the TITLE (strong on their own).
FRESHER_TITLE_WORDS = ["intern", "new grad", "new-grad", "graduate engineer",
                       "graduate software", "trainee", "apprentice",
                       "campus", "entry level", "entry-level", "fresher",
                       "associate engineer", "early career", "early talent"]
# First-job signals in the BODY. Strict phrases only: bare words like
# "graduate"/"campus" appear in every JD's education section, so we avoid them.
FRESHER_BODY_WORDS = ["0-1 year", "0-2 year", "0 to 1 year", "0 to 2 year",
                      "no prior experience", "no professional experience",
                      "recent graduate", "recent graduates", "fresh graduate",
                      "fresher", "final year student", "entry level",
                      "entry-level", "new graduate"]

# A level suffix like "Engineer 2", "Developer III" -> not a first job.
LEVEL_RE = re.compile(r"\b(?:ii|iii|iv|v|[2-9])\s*$", re.I)
# Title experience requirement, e.g. "4-8yrs", "5+ years".
EXP_TITLE_RE = re.compile(r"\d+\s*(?:\+|-|–|to)?\s*\d*\s*(?:yr|year)", re.I)
# Body experience requirement of 3+ years (0-2 yrs is fine for freshers).
EXP_BODY_RE = re.compile(
    r"\b([3-9]|1\d|2\d)\s*\+?\s*(?:-|to|–)?\s*\d*\s*\+?\s*years?", re.I)


def is_fresher(title, body=""):
    t = title.lower()
    if any(w in t for w in FRESHER_TITLE_WORDS):
        return True
    return any(w in body.lower() for w in FRESHER_BODY_WORDS)


def ats_keep(title, location, body=""):
    """Keep India-located CSE/AI roles open to first-job freshers.

    Senior level, level suffixes, and a 3-plus-year experience requirement
    (read from the job description, not just the title) are hard rejects.
    """
    t = title.lower()
    loc = (location or "").lower()
    if not any(h in loc for h in INDIA_HINTS):
        return False
    if not any(w in t for w in TECH_WORDS):   # CSE/AI-relevant roles only
        return False
    if EXP_TITLE_RE.search(title) or EXP_BODY_RE.search(body):
        return False                  # requires 3+ years -> not a first job
    if any(w in t for w in SENIOR_WORDS):
        return False                  # senior/staff/principal/manager/lead
    if LEVEL_RE.search(t.strip()):    # "Engineer 2/3", "Developer III"
        return False
    return True


def load_queries():
    """Return list of (category, query)."""
    out = []
    with open(QUERIES_FILE, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            if "::" in line:
                cat, q = line.split("::", 1)
                out.append((cat.strip() or "General", q.strip()))
            else:
                out.append(("General", line))
    return out


def load_sources():
    """Return list of (category, provider, token) from sources.txt."""
    out = []
    if not os.path.exists(SOURCES_FILE):
        return out
    with open(SOURCES_FILE, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = [p.strip() for p in line.split("::")]
            if len(parts) == 3 and parts[1] and parts[2]:
                out.append((parts[0] or "Official Openings",
                            parts[1].lower(), parts[2]))
    return out


def parse_iso(s):
    if not isinstance(s, str) or not s:
        return None
    try:
        d = datetime.fromisoformat(s.replace("Z", "+00:00"))
        return d if d.tzinfo else d.replace(tzinfo=timezone.utc)
    except ValueError:
        return None


def parse_date(v):
    """Parse a platform 'posted' value into an aware datetime.

    Greenhouse gives an ISO-8601 string (first_published); Lever gives epoch
    milliseconds as an int (createdAt). Handle both, return None on junk.
    """
    if isinstance(v, (int, float)):
        try:
            return datetime.fromtimestamp(v / 1000, tz=timezone.utc)
        except (OverflowError, OSError, ValueError):
            return None
    return parse_iso(v)


def strip_html(s):
    return " ".join(re.sub(r"<[^>]+>", " ", html.unescape(s or "")).split())


def flatten_loc(v):
    """ATS location fields are a string for some providers and a nested dict
    for others (SmartRecruiters). Always return a string so ats_keep, which
    does location.lower(), never hits AttributeError and drops the source.
    """
    if isinstance(v, str):
        s = v
    elif isinstance(v, dict):
        s = (v.get("fullLocation") or v.get("name")
             or ", ".join(str(p) for p in
                          (v.get("city"), v.get("region"), v.get("country")) if p))
    else:
        return ""
    # Some feeds carry stray slashes in region codes (e.g. "//TN"); tidy them.
    return re.sub(r"\s+", " ", (s or "").replace("/", " ")).strip()


def fetch_greenhouse(token):
    """Genuine openings from a company's Greenhouse board (no key needed).

    Pulls full job descriptions (content=true) so we can detect the real
    experience requirement, which the title alone rarely states.
    """
    data = json.loads(fetch(
        f"https://boards-api.greenhouse.io/v1/boards/{token}/jobs?content=true"))
    out = []
    for j in data.get("jobs", []):
        out.append({"title": (j.get("title") or "").strip(),
                    "link": j.get("absolute_url", ""),
                    "location": (j.get("location") or {}).get("name", ""),
                    "body": strip_html(j.get("content")),
                    "source": token.replace("-", " ").title(),
                    "published": parse_date(j.get("first_published")
                                            or j.get("updated_at"))})
    return out


def fetch_lever(token):
    """Genuine openings from a company's Lever board (no key needed)."""
    data = json.loads(fetch(
        f"https://api.lever.co/v0/postings/{token}?mode=json"))
    out = []
    for j in data:
        cats = j.get("categories") or {}
        out.append({"title": (j.get("text") or "").strip(),
                    "link": j.get("hostedUrl", ""),
                    "location": cats.get("location", "") or "",
                    "body": j.get("descriptionPlain", "") or "",
                    "source": token.replace("-", " ").title(),
                    "published": parse_date(j.get("createdAt"))})
    return out


def fetch_ashby(token):
    """Openings from a company's Ashby board (no key needed).

    The public posting API returns descriptionPlain, so the experience filter
    can read the real requirement from the job description, like Greenhouse.
    """
    data = json.loads(fetch(
        f"https://api.ashbyhq.com/posting-api/job-board/{token}"))
    out = []
    for j in data.get("jobs", []):
        if j.get("isListed") is False:        # hidden/unlisted posting
            continue
        out.append({"title": (j.get("title") or "").strip(),
                    "link": j.get("jobUrl") or j.get("applyUrl") or "",
                    "location": flatten_loc(j.get("location")),
                    "body": j.get("descriptionPlain") or "",
                    "source": token.replace("-", " ").title(),
                    "published": parse_date(j.get("publishedAt"))})
    return out


def fetch_smartrecruiters(token):
    """Openings from a company's SmartRecruiters board (no key needed).

    The postings listing carries no job description, so filtering here is
    title + location only. SmartRecruiters states seniority in the title
    (e.g. 'Sr. Manager'), which SENIOR_WORDS already catches. Reads the first
    page (up to 100 postings); India roles are kept by ats_keep downstream.
    """
    data = json.loads(fetch(
        "https://api.smartrecruiters.com/v1/companies/"
        f"{token}/postings?limit=100"))
    out = []
    for j in data.get("content", []):
        jid = j.get("id", "")
        out.append({"title": (j.get("name") or "").strip(),
                    "link": f"https://jobs.smartrecruiters.com/{token}/{jid}",
                    "location": flatten_loc(j.get("location")),
                    "body": "",
                    "source": token.replace("-", " ").title(),
                    "published": parse_date(j.get("releasedDate"))})
    return out


def fetch_recruitee(token):
    """Openings from a company's Recruitee board (no key needed)."""
    data = json.loads(fetch(f"https://{token}.recruitee.com/api/offers/"))
    out = []
    for j in data.get("offers", []):
        loc = ", ".join(str(p) for p in (j.get("city"), j.get("country")) if p)
        out.append({"title": (j.get("title") or "").strip(),
                    "link": j.get("careers_apply_url") or j.get("careers_url") or "",
                    "location": loc,
                    "body": strip_html(j.get("description")),
                    "source": token.replace("-", " ").title(),
                    "published": parse_date(j.get("published_at")
                                            or j.get("created_at"))})
    return out


FETCHERS = {"greenhouse": fetch_greenhouse, "lever": fetch_lever,
            "ashby": fetch_ashby, "smartrecruiters": fetch_smartrecruiters,
            "recruitee": fetch_recruitee}


def load_json(path, default):
    if os.path.exists(path):
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    return default


def save_json(path, data):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False)


def fetch(url):
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=30) as r:
        return r.read()


def parse_rss(xml_bytes):
    items = []
    try:
        root = ET.fromstring(xml_bytes)
    except ET.ParseError:
        return items
    for item in root.iter("item"):
        title = (item.findtext("title") or "").strip()
        link = (item.findtext("link") or "").strip()
        pub = item.findtext("pubDate")
        source = (item.findtext("source") or "").strip()
        published = None
        if pub:
            try:
                published = datetime.strptime(pub.strip(),
                                              "%a, %d %b %Y %H:%M:%S %Z")
                published = published.replace(tzinfo=timezone.utc)
            except ValueError:
                published = None
        if title and link:
            items.append({"title": title, "link": link,
                          "published": published, "source": source})
    return items


def is_fresh(item):
    if item["published"] is None:
        return True
    return datetime.now(timezone.utc) - item["published"] <= timedelta(days=MAX_AGE_DAYS)


def link_id(link):
    return hashlib.sha1(link.encode("utf-8")).hexdigest()


def clean_title(t):
    return re.sub(r"\s+", " ", t)[:220]


def telegram_send(text, token, chat_id, dry_run=False):
    if dry_run:
        print("---- DRY RUN MESSAGE ----")
        print(text)
        return True
    url = f"https://api.telegram.org/bot{token}/sendMessage"
    data = urllib.parse.urlencode({"chat_id": chat_id, "text": text,
                                   "disable_web_page_preview": "true"}).encode()
    req = urllib.request.Request(url, data=data, headers={"User-Agent": UA})
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            return r.status == 200
    except Exception as e:
      import traceback
      traceback.print_exc()
      print(f"Telegram send failed: {repr(e)}", file=sys.stderr)
      return False

def chunk_messages(header, lines, limit=3500):
    current = header
    for line in lines:
        if len(current) + len(line) + 2 > limit:
            yield current
            current = header + " (contd.)\n" + line
        else:
            current += "\n" + line
    if current.strip():
        yield current


def fmt_posted(iso):
    """Absolute date a job went live on its ATS, e.g. '24 Jun 2026'."""
    try:
        d = datetime.fromisoformat(iso)
    except (ValueError, TypeError):
        return ""
    if d.tzinfo is None:
        d = d.replace(tzinfo=timezone.utc)
    return d.astimezone(IST).strftime("%d %b %Y")


def age_label(iso, now):
    then = datetime.fromisoformat(iso)
    mins = int((now - then).total_seconds() // 60)
    if mins < 60:
        return f"{max(mins, 1)} min ago"
    hrs = mins // 60
    if hrs < 24:
        return f"{hrs} hr ago"
    return f"{hrs // 24} d ago"


def render_portal(jobs, now):
    new_cut = now - timedelta(hours=24)
    total = len(jobs)
    new24 = sum(1 for j in jobs
                if datetime.fromisoformat(j["first_seen"]) >= new_cut)
    updated = now.strftime("%d %b %Y, %I:%M %p IST")

    cats = [c for c in CATEGORY_ORDER
            if any(j["category"] == c for j in jobs)]
    chips = ['<button class="chip active" data-f="all">All</button>',
             '<button class="chip" data-f="new">New 24h</button>',
             '<button class="chip" data-f="fresher">Freshers</button>']
    chips += [f'<button class="chip" data-f="{html.escape(c)}">{html.escape(c)}</button>'
              for c in cats]

    sections = []
    for cat in cats:
        items = sorted([j for j in jobs if j["category"] == cat],
                       key=lambda j: j["first_seen"], reverse=True)
        cards = []
        for j in items:
            is_new = datetime.fromisoformat(j["first_seen"]) >= new_cut
            badge = '<span class="new">NEW</span>' if is_new else ""
            if j.get("fresher"):
                badge += '<span class="fresher">FRESHER</span>'
            src = f'<span>{html.escape(j["source"])}</span> · ' if j["source"] else ""
            if j.get("location"):
                src += f'<span>{html.escape(j["location"])}</span> · '
            posted = fmt_posted(j.get("posted")) if j.get("posted") else ""
            if posted:
                src += f'<span>posted {posted}</span> · '
            cards.append(
                f'<article class="card" data-cat="{html.escape(cat)}" '
                f'data-new="{1 if is_new else 0}" '
                f'data-fresher="{1 if j.get("fresher") else 0}">'
                f'<a href="{html.escape(j["link"])}" target="_blank" rel="noopener">'
                f'{html.escape(j["title"])}</a>{badge}'
                f'<div class="meta">{src}<span>spotted {age_label(j["first_seen"], now)}</span></div>'
                f'</article>')
        color = CATEGORY_COLOR.get(cat, "#5a5247")
        sections.append(
            f'<section class="cat" data-cat="{html.escape(cat)}" style="--cc:{color}">'
            f'<h2>{html.escape(cat)} <small>{len(items)}</small></h2>'
            + "".join(cards) + "</section>")

    return f"""<!doctype html>
<html lang="en"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>RBCET Placement Board</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Fraunces:opsz,wght@9..144,700;9..144,900&family=IBM+Plex+Sans:wght@400;600&display=swap" rel="stylesheet">
<style>
:root{{--paper:#f7f1e5;--ink:#1b2433;--accent:#d96f1e;--muted:#6f6757;--card:#fffdf7}}
*{{box-sizing:border-box}}
body{{margin:0;background:var(--paper);color:var(--ink);
 font:16px/1.5 "IBM Plex Sans",sans-serif;
 background-image:radial-gradient(#00000010 1px,transparent 1px);
 background-size:22px 22px}}
header{{border-bottom:3px double var(--ink);padding:26px 16px 14px;
 max-width:880px;margin:0 auto}}
h1{{font-family:Fraunces,serif;font-weight:900;font-size:clamp(30px,6vw,52px);
 margin:0;letter-spacing:-.02em}}
h1 em{{color:var(--accent);font-style:normal}}
.sub{{color:var(--muted);font-size:14px;margin-top:6px}}
.sub b{{color:var(--ink)}}
.bar{{position:sticky;top:0;background:var(--paper);z-index:5;
 border-bottom:1px solid #00000022;padding:10px 16px;max-width:880px;margin:0 auto}}
.chips{{display:flex;gap:8px;overflow-x:auto;padding-bottom:6px}}
.chip{{font:600 13px "IBM Plex Sans",sans-serif;border:1.5px solid var(--ink);
 background:transparent;color:var(--ink);padding:6px 12px;border-radius:999px;
 cursor:pointer;white-space:nowrap}}
.chip.active{{background:var(--ink);color:var(--paper)}}
#q{{width:100%;margin-top:8px;padding:9px 12px;border:1.5px solid var(--ink);
 border-radius:8px;background:var(--card);font:inherit}}
main{{max-width:880px;margin:0 auto;padding:8px 16px 40px}}
.cat h2{{font-family:Fraunces,serif;font-weight:700;font-size:22px;
 border-left:6px solid var(--cc);padding-left:10px;margin:26px 0 10px}}
.cat h2 small{{color:var(--muted);font:600 13px "IBM Plex Sans",sans-serif}}
.card{{background:var(--card);border:1px solid #00000018;border-left:4px solid var(--cc);
 border-radius:8px;padding:12px 14px;margin:8px 0;box-shadow:2px 2px 0 #00000010}}
.card a{{color:var(--ink);font-weight:600;text-decoration:none}}
.card a:hover{{text-decoration:underline;text-decoration-color:var(--accent)}}
.meta{{color:var(--muted);font-size:13px;margin-top:4px}}
.new{{background:var(--accent);color:#fff;font:700 11px "IBM Plex Sans",sans-serif;
 padding:2px 7px;border-radius:4px;margin-left:8px;vertical-align:2px}}
.fresher{{background:#2f6f6f;color:#fff;font:700 11px "IBM Plex Sans",sans-serif;
 padding:2px 7px;border-radius:4px;margin-left:8px;vertical-align:2px}}
.hide{{display:none}}
footer{{max-width:880px;margin:0 auto;padding:18px 16px 50px;color:var(--muted);
 font-size:13px;border-top:3px double var(--ink)}}
footer a{{color:var(--accent)}}
</style></head><body>
<header>
 <h1>RBCET <em>Placement</em> Board</h1>
 <div class="sub">Dept. of CSE/AI · auto-refreshed 4&times; daily ·
  last update <b>{updated}</b> · <b>{total}</b> postings ·
  <b>{new24}</b> new in 24h</div>
</header>
<div class="bar">
 <div class="chips">{''.join(chips)}</div>
 <input id="q" type="search" placeholder="Search company or keyword&hellip;">
</div>
<main>{''.join(sections)}</main>
<footer>Always apply on the company's official career page (these links are
announcements, not application forms). Get instant push alerts on
<a href="{TELEGRAM_LINK}">Telegram</a>. Sources: public news feeds; drive dates
must be verified on official portals.</footer>
<script>
var f="all";
function apply(){{var q=document.getElementById("q").value.toLowerCase();
 document.querySelectorAll(".card").forEach(function(c){{
  var ok=(f==="all")||(f==="new"&&c.dataset.new==="1")||(f==="fresher"&&c.dataset.fresher==="1")||(c.dataset.cat===f);
  if(ok&&q)ok=c.textContent.toLowerCase().indexOf(q)>-1;
  c.classList.toggle("hide",!ok);}});
 document.querySelectorAll(".cat").forEach(function(s){{
  s.classList.toggle("hide",
   s.querySelectorAll(".card:not(.hide)").length===0);}});}}
document.querySelectorAll(".chip").forEach(function(ch){{
 ch.onclick=function(){{document.querySelectorAll(".chip")
  .forEach(function(x){{x.classList.remove("active")}});
  ch.classList.add("active");f=ch.dataset.f;apply();}}}});
document.getElementById("q").oninput=apply;
</script></body></html>"""


def main():
    dry_run = os.environ.get("DRY_RUN") == "1"
    token = os.environ.get("TELEGRAM_BOT_TOKEN", "")
    chat_id = os.environ.get("TELEGRAM_CHAT_ID", "")
    if not dry_run and (not token or not chat_id):
        print("Missing TELEGRAM_BOT_TOKEN / TELEGRAM_CHAT_ID", file=sys.stderr)
        sys.exit(1)

    now = datetime.now(IST)
    seen = load_json(SEEN_FILE, [])
    seen_set = set(seen)
    jobs = [j for j in load_json(JOBS_FILE, [])
            if j.get("official") or is_relevant(j["title"])]
    titles_seen = {norm_title(j["title"]) for j in jobs}
    new_lines = []

    for category, query in load_queries():
        url = ("https://news.google.com/rss/search?q="
               + urllib.parse.quote(query) + "&hl=en-IN&gl=IN&ceid=IN:en")
        try:
            xml_bytes = fetch(url)
        except Exception as e:
            print(f"Fetch failed for '{query}': {e}", file=sys.stderr)
            continue
        count = 0
        for item in parse_rss(xml_bytes):
            if count >= MAX_ITEMS_PER_QUERY:
                break
            if not is_fresh(item):
                continue
            lid = link_id(item["link"])
            if lid in seen_set:
                continue
            seen_set.add(lid)
            seen.append(lid)
            title = clean_title(item["title"])
            nt = norm_title(title)
            if not is_relevant(title) or nt in titles_seen:
                continue
            titles_seen.add(nt)
            jobs.append({"id": lid, "title": title, "link": item["link"],
                         "source": item["source"], "category": category,
                         "first_seen": now.isoformat()})
            src = f" ({item['source']})" if item["source"] else ""
            new_lines.append(f"[{category}] {title}{src}\n{item['link']}")
            count += 1

    # ---- Official company boards (genuine openings, direct apply links) ----
    for category, provider, source_token in load_sources():
        fn = FETCHERS.get(provider)
        if not fn:
            print(f"Unknown source provider: {provider}", file=sys.stderr)
            continue
        try:
            items = fn(source_token)
        except Exception as e:
            print(f"Source failed {provider}/{source_token}: {e}", file=sys.stderr)
            continue
        kept = 0
        for item in items:
            body = item.get("body", "")
            if not ats_keep(item["title"], item.get("location", ""), body):
                continue
            lid = link_id(item["link"])
            if lid in seen_set:
                continue
            seen_set.add(lid)
            seen.append(lid)
            title = clean_title(item["title"])
            nt = norm_title(title)
            if nt in titles_seen:
                continue
            titles_seen.add(nt)
            loc = item.get("location", "")
            fresher = is_fresher(title, body)
            posted = item.get("published")
            posted_iso = posted.isoformat() if posted else None
            jobs.append({"id": lid, "title": title, "link": item["link"],
                         "source": item["source"], "category": category,
                         "official": True, "fresher": fresher, "location": loc,
                         "posted": posted_iso, "first_seen": now.isoformat()})
            extra = f", {loc}" if loc else ""
            tag = "[Fresher] " if fresher else ""
            when = f" · posted {fmt_posted(posted_iso)}" if posted_iso else ""
            new_lines.append(
                f"[{category}] {tag}{title} ({item['source']}{extra}){when}\n{item['link']}")
            kept += 1
        print(f"{provider}/{token}: {kept} new official opening(s)",
              file=sys.stderr)

    # prune portal data
    cutoff = now - timedelta(days=KEEP_DAYS)
    jobs = [j for j in jobs
            if datetime.fromisoformat(j["first_seen"]) >= cutoff][-MAX_JOBS:]

    os.makedirs("docs", exist_ok=True)
    with open(PORTAL_FILE, "w", encoding="utf-8") as fh:
        fh.write(render_portal(jobs, now))
    save_json(JOBS_FILE, jobs)

    if not new_lines:
        save_json(SEEN_FILE, seen[-MAX_SEEN:])
        print("No new postings; portal refreshed.")
        return

    header = f"NEW PLACEMENT ALERTS - {now.strftime('%d %b %Y, %I:%M %p')} IST"
    ok = True
    for msg in chunk_messages(header, new_lines):
        ok = telegram_send(msg, token, chat_id, dry_run) and ok
    if ok:
        save_json(SEEN_FILE, seen[-MAX_SEEN:])
        print(f"Sent {len(new_lines)} new item(s); portal refreshed.")
    else:
        print("Some sends failed; will retry next run.", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
