#!/usr/bin/env python3
"""
Facebook Marketplace Monitor
Continuously scrapes Facebook Marketplace and sends alerts when listings match
your price range and keyword criteria.

DISCLAIMER:
    Automated access to Facebook may violate their Terms of Service.
    Use this tool for personal, non-commercial purposes only and at your own risk.

DEPENDENCIES (install with pip):
    pip install undetected-chromedriver selenium plyer

    undetected-chromedriver  — stealth Chrome driver that avoids bot detection
    selenium                 — browser automation
    plyer                    — cross-platform desktop notifications (optional)

    Also requires Google Chrome to be installed on your system.

QUICK START:
    python fbm_monitor.py                                    # interactive wizard (supports multiple queries)
    python fbm_monitor.py --keyword "iPhone 14" --min-price 400 --max-price 700
    python fbm_monitor.py --queries my_searches.json         # load a multi-query file
    python fbm_monitor.py --config my_search.json            # reload a single saved search

ALL OPTIONS:
    --keyword           Primary search term (single query)
    --min-price         Minimum listing price
    --max-price         Maximum listing price
    --extra-keywords    Additional words that must appear in the title
    --radius            Search radius in miles
    --interval          Seconds between full scan cycles (default: 120)
    --discord-webhook   Discord webhook URL for rich embed alerts
    --email             Facebook login email
    --password          Facebook login password (avoid: appears in shell history)
    --queries           Path to a multi-query JSON file (fbm_queries.json format)
    --config            Path to a single saved query JSON file (backward-compat)
    --headless          Run Chrome with a visible window
    --verbose           Enable debug-level logging

STOPPING:
    Press Ctrl+C at any time. The monitor shuts down gracefully.

FILES CREATED AT RUNTIME:
    .env              — Facebook email & password (created on first run, keep private!)
    fbm_queries.json  — saved multi-query parameters (preferred)
    fbm_config.json   — saved single-query parameters (legacy/backward-compat)
    fbm_seen.json     — seen listing IDs (prevents duplicate alerts, shared across queries)
    fbm_cookies.json  — Facebook session cookies (skips re-login)
    fbm_monitor.log   — rolling log file

CREDENTIALS (.env):
    The monitor looks for credentials in this order:
      1. --email / --password CLI flags
      2. .env file  (FBM_EMAIL=... / FBM_PASSWORD=...)
      3. FBM_EMAIL / FBM_PASSWORD environment variables
      4. Interactive prompt (offers to save to .env afterward)
    Keep .env private — add it to .gitignore and do not share it.

MULTI-QUERY FILE FORMAT (fbm_queries.json):
    {
      "scan_interval": 120,
      "queries": [
        {"keyword": "iPhone 14",   "min_price": 400, "max_price": 700,  "discord_webhook": "https://..."},
        {"keyword": "bicycle",     "min_price": 0,   "max_price": 300,  "discord_webhook": null},
        {"keyword": "MacBook Pro", "min_price": 800, "max_price": 1500, "extra_keywords": ["M1", "M2"]}
      ]
    }
"""

from __future__ import annotations  # allows | union hints on Python 3.8/3.9

import argparse
import getpass
import json
import logging
import os
import random
import re
import signal
import smtplib
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime
from email.mime.text import MIMEText
from pathlib import Path
from threading import Event

# ─── Browser imports ──────────────────────────────────────────────────────────
# Prefer undetected-chromedriver, fall back to plain selenium.

try:
    import undetected_chromedriver as uc
    HAS_UC = True
except ImportError:
    HAS_UC = False

try:
    from selenium import webdriver
    from selenium.webdriver.chrome.options import Options as ChromeOptions
    from selenium.webdriver.common.by import By
    from selenium.webdriver.common.keys import Keys
    from selenium.webdriver.support.ui import WebDriverWait
    from selenium.webdriver.support import expected_conditions as EC
    from selenium.common.exceptions import (
        NoSuchElementException,
        StaleElementReferenceException,
        TimeoutException,
        WebDriverException,
    )
except ImportError:
    print("ERROR: selenium is not installed.\nRun: pip install selenium undetected-chromedriver")
    sys.exit(1)

# ─── Notification import ──────────────────────────────────────────────────────

try:
    from plyer import notification as plyer_notify  # type: ignore
    HAS_PLYER = True
except ImportError:
    HAS_PLYER = False


# ─── Constants ────────────────────────────────────────────────────────────────

VERSION = "1.0.0"
FB_BASE = "https://www.facebook.com"
FB_LOGIN_URL = "https://www.facebook.com/login"
FB_SEARCH_URL = "https://www.facebook.com/marketplace/search/"

CONFIG_PATH = Path("fbm_config.json")    # single-query legacy format
QUERIES_PATH = Path("fbm_queries.json")  # multi-query format (preferred)
SEEN_PATH = Path("fbm_seen.json")
COOKIES_PATH = Path("fbm_cookies.json")
ENV_PATH = Path(".env")                  # stores FBM_EMAIL / FBM_PASSWORD

DEFAULT_SCAN_INTERVAL = 120  # seconds between scans
MAX_SEEN_IDS = 5_000         # cap stored IDs to prevent unbounded growth

# Rotate user-agent strings to reduce fingerprinting
USER_AGENTS = [
    (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/124.0.0.0 Safari/537.36"
    ),
    (
        "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/124.0.0.0 Safari/537.36"
    ),
    (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/123.0.0.0 Safari/537.36"
    ),
]


# ─── Logging ──────────────────────────────────────────────────────────────────

def setup_logging(verbose: bool = False) -> logging.Logger:
    level = logging.DEBUG if verbose else logging.INFO
    fmt = "%(asctime)s [%(levelname)s] %(message)s"
    handlers: list[logging.Handler] = [
        logging.StreamHandler(sys.stdout),
        logging.FileHandler("fbm_monitor.log", encoding="utf-8"),
    ]
    logging.basicConfig(level=level, format=fmt, handlers=handlers, force=True)
    if not verbose:
        # Suppress chatty third-party logs
        for noisy in ("selenium", "urllib3", "undetected_chromedriver"):
            logging.getLogger(noisy).setLevel(logging.WARNING)
    return logging.getLogger("fbm")


# ─── Search Config ────────────────────────────────────────────────────────────

class SearchConfig:
    """All user-specified parameters for a marketplace search."""

    def __init__(
        self,
        keyword: str,
        min_price: float | None = None,
        max_price: float | None = None,
        extra_keywords: list[str] | None = None,
        radius: int | None = None,
        scan_interval: int = DEFAULT_SCAN_INTERVAL,
        discord_webhook: str | None = None,
        email_config: dict | None = None,
    ):
        self.keyword = keyword.strip()
        self.min_price = min_price
        self.max_price = max_price
        self.extra_keywords = [k.lower().strip() for k in (extra_keywords or []) if k.strip()]
        self.radius = radius
        self.scan_interval = max(30, scan_interval)  # floor at 30s to be respectful
        self.discord_webhook = discord_webhook or None
        self.email_config: dict = email_config or {}

    # ── Serialisation ─────────────────────────────────────────────────────────

    def to_dict(self) -> dict:
        return {
            "keyword": self.keyword,
            "min_price": self.min_price,
            "max_price": self.max_price,
            "extra_keywords": self.extra_keywords,
            "radius": self.radius,
            "scan_interval": self.scan_interval,
            "discord_webhook": self.discord_webhook,
            "email_config": self.email_config,
        }

    @classmethod
    def from_dict(cls, d: dict) -> SearchConfig:
        return cls(
            keyword=d.get("keyword", ""),
            min_price=d.get("min_price"),
            max_price=d.get("max_price"),
            extra_keywords=d.get("extra_keywords", []),
            radius=d.get("radius"),
            scan_interval=d.get("scan_interval", DEFAULT_SCAN_INTERVAL),
            discord_webhook=d.get("discord_webhook"),
            email_config=d.get("email_config", {}),
        )

    def save(self, path: Path = CONFIG_PATH) -> None:
        path.write_text(json.dumps(self.to_dict(), indent=2))

    @classmethod
    def load(cls, path: Path) -> SearchConfig:
        return cls.from_dict(json.loads(path.read_text()))

    @classmethod
    def save_queries(
        cls,
        configs: list[SearchConfig],
        scan_interval: int,
        path: Path = QUERIES_PATH,
    ) -> None:
        """Serialise a list of queries plus a global cycle interval to disk."""
        path.write_text(json.dumps({
            "scan_interval": scan_interval,
            "queries": [c.to_dict() for c in configs],
        }, indent=2))

    @classmethod
    def load_queries(cls, path: Path = QUERIES_PATH) -> tuple[list[SearchConfig], int]:
        """
        Load a multi-query file.  Returns (configs, scan_interval).
        The top-level scan_interval governs the whole cycle; per-query
        scan_interval fields (written by to_dict for backward compat) are ignored.
        """
        data = json.loads(path.read_text())
        interval = int(data.get("scan_interval", DEFAULT_SCAN_INTERVAL))
        configs = [cls.from_dict(q) for q in data.get("queries", [])]
        if not configs:
            raise ValueError(f"No queries found in {path}")
        return configs, interval

    # ── URL builder ───────────────────────────────────────────────────────────

    def build_search_url(self) -> str:
        """Construct the Marketplace search URL from current parameters."""
        params: dict = {
            "query": self.keyword,
            "sortBy": "creation_time_descend",  # newest first
            "exact": "false",
        }
        if self.min_price is not None:
            params["minPrice"] = int(self.min_price)
        if self.max_price is not None:
            params["maxPrice"] = int(self.max_price)
        if self.radius is not None:
            params["radius"] = self.radius
        return FB_SEARCH_URL + "?" + urllib.parse.urlencode(params)

    # ── Matching logic ────────────────────────────────────────────────────────

    def matches(self, listing: Listing) -> bool:
        """Return True if the listing satisfies every filter criterion."""
        title_lower = listing.title.lower()

        if self.keyword.lower() not in title_lower:
            return False

        for kw in self.extra_keywords:
            if kw not in title_lower:
                return False

        if listing.price is not None:
            if self.min_price is not None and listing.price < self.min_price:
                return False
            if self.max_price is not None and listing.price > self.max_price:
                return False
        else:
            # Unknown price: skip when a price range is required
            if self.min_price is not None or self.max_price is not None:
                return False

        return True


# ─── Listing ──────────────────────────────────────────────────────────────────

class Listing:
    """One Facebook Marketplace listing."""

    def __init__(
        self,
        listing_id: str,
        title: str,
        price: float | None,
        url: str,
        location: str = "",
    ):
        self.listing_id = listing_id
        self.title = title
        self.price = price
        self.url = url
        self.location = location
        self.found_at = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    @property
    def price_str(self) -> str:
        if self.price is None:
            return "Price unknown"
        if self.price == 0:
            return "Free"
        return f"${self.price:,.0f}"

    def summary(self) -> str:
        lines = [
            f"Title    : {self.title}",
            f"Price    : {self.price_str}",
        ]
        if self.location:
            lines.append(f"Location : {self.location}")
        lines.append(f"Link     : {self.url}")
        lines.append(f"Found at : {self.found_at}")
        return "\n".join(lines)

    def __repr__(self) -> str:
        return f"Listing({self.listing_id!r}, {self.title!r}, {self.price_str})"


# ─── Seen-Listing Tracker ─────────────────────────────────────────────────────

class SeenTracker:
    """
    Persists seen listing IDs to disk so the monitor does not re-alert on items
    it already reported in a previous scan or a previous run.
    """

    def __init__(self, path: Path = SEEN_PATH):
        self.path = path
        self._ids: set[str] = set()
        self._load()

    def _load(self) -> None:
        if self.path.exists():
            try:
                data = json.loads(self.path.read_text())
                self._ids = set(data.get("seen", []))
            except (json.JSONDecodeError, OSError):
                self._ids = set()

    def _save(self) -> None:
        # Trim to the most recent MAX_SEEN_IDS entries
        trimmed = list(self._ids)[-MAX_SEEN_IDS:]
        self._ids = set(trimmed)
        try:
            self.path.write_text(json.dumps({"seen": trimmed}, indent=2))
        except OSError:
            pass

    def is_new(self, listing_id: str) -> bool:
        return listing_id not in self._ids

    def mark_seen(self, listing_id: str) -> None:
        self._ids.add(listing_id)
        self._save()


# ─── Notifier ─────────────────────────────────────────────────────────────────

class Notifier:
    """
    Dispatches alerts through every configured channel.

    Config is NOT stored at construction time — it is passed into notify()
    on each call so that per-query webhook/email settings are routed correctly
    when running multiple queries in a single session.
    """

    def __init__(self, log: logging.Logger):
        self.log = log

    def notify(self, listing: Listing, config: SearchConfig) -> None:
        """Send an alert for `listing` using the channels configured in `config`."""
        self._console(listing)
        if HAS_PLYER:
            self._desktop(listing)
        if config.discord_webhook:
            self._discord(listing, config)
        if config.email_config:
            self._email(listing, config)

    # ── Channels ──────────────────────────────────────────────────────────────

    def _console(self, listing: Listing) -> None:
        border = "=" * 62
        self.log.info(
            "\n%s\n  MATCH FOUND!\n%s\n%s\n%s",
            border, border, listing.summary(), border,
        )

    def _desktop(self, listing: Listing) -> None:
        try:
            plyer_notify.notify(
                title=f"FBM Alert — {listing.price_str}",
                message=listing.title[:200],
                app_name="FBM Monitor",
                timeout=12,
            )
        except Exception as exc:
            self.log.debug("Desktop notification failed: %s", exc)

    def _discord(self, listing: Listing, config: SearchConfig) -> None:
        # "content": null alongside embeds can trigger Discord validation errors;
        # omit it entirely and let the embed stand on its own.
        payload = json.dumps({
            "embeds": [{
                "title": listing.title[:256],
                "url": listing.url,
                "color": 5_814_783,  # blue
                "fields": [
                    {"name": "Price",    "value": listing.price_str,          "inline": True},
                    {"name": "Location", "value": listing.location or "N/A",  "inline": True},
                ],
                "footer": {"text": f"FBM Monitor v{VERSION} • {listing.found_at}"},
            }],
        }).encode("utf-8")
        try:
            req = urllib.request.Request(
                config.discord_webhook,
                data=payload,
                headers={
                    "Content-Type": "application/json",
                    # Discord blocks requests without a recognisable User-Agent (returns 403)
                    "User-Agent": f"FBMMonitor/{VERSION} (Python urllib)",
                },
                method="POST",
            )
            with urllib.request.urlopen(req, timeout=10) as resp:
                self.log.debug("Discord notification sent (HTTP %s).", resp.status)
        except urllib.error.HTTPError as exc:
            # Read the response body — Discord includes a descriptive error message
            body = exc.read().decode("utf-8", errors="replace")
            self.log.warning("Discord notification failed: HTTP %s %s — %s", exc.code, exc.reason, body)
        except Exception as exc:
            self.log.warning("Discord notification failed: %s", exc)

    def _email(self, listing: Listing, config: SearchConfig) -> None:
        ec = config.email_config
        required = ("smtp_host", "smtp_port", "username", "password", "to")
        if not all(k in ec for k in required):
            return
        try:
            msg = MIMEText(listing.summary())
            msg["Subject"] = f"FBM Alert: {listing.title} — {listing.price_str}"
            msg["From"] = ec["username"]
            msg["To"] = ec["to"]
            with smtplib.SMTP_SSL(ec["smtp_host"], int(ec["smtp_port"])) as server:
                server.login(ec["username"], ec["password"])
                server.send_message(msg)
            self.log.debug("Email notification sent.")
        except Exception as exc:
            self.log.warning("Email notification failed: %s", exc)


# ─── Browser ──────────────────────────────────────────────────────────────────

class Browser:
    """Creates and manages the Chrome browser instance."""

    def __init__(self, headless: bool = False, log: logging.Logger | None = None):
        self.headless = headless
        self.log = log or logging.getLogger("fbm")
        self.driver = None

    def _make_options(self):
        if HAS_UC:
            options = uc.ChromeOptions()
        else:
            options = ChromeOptions()
            # Regular selenium needs these flags set explicitly
            options.add_experimental_option("excludeSwitches", ["enable-automation"])
            options.add_experimental_option("useAutomationExtension", False)

        options.add_argument("--no-sandbox")
        options.add_argument("--disable-dev-shm-usage")
        options.add_argument("--disable-blink-features=AutomationControlled")
        options.add_argument(f"--user-agent={random.choice(USER_AGENTS)}")
        options.add_argument("--window-size=1366,768")
        options.add_argument("--lang=en-US,en;q=0.9")

        if self.headless:
            # headless=new is Chrome's modern headless mode (less detectable)
            options.add_argument("--headless=new")

        return options

    def start(self):
        impl = "undetected-chromedriver" if HAS_UC else "selenium WebDriver"
        self.log.info("Starting browser (%s)…", impl)
        options = self._make_options()
        if HAS_UC:
            self.driver = uc.Chrome(options=options, use_subprocess=True)
        else:
            self.driver = webdriver.Chrome(options=options)
        # Remove the automation property injected by the default chromedriver
        self.driver.execute_script(
            "Object.defineProperty(navigator, 'webdriver', {get: () => undefined})"
        )
        self.log.info("Browser ready.")
        return self.driver

    def quit(self) -> None:
        if self.driver:
            try:
                self.driver.quit()
            except Exception:
                pass
            self.driver = None

    # ── Cookie persistence (keeps Facebook session alive across runs) ──────────

    def save_cookies(self, path: Path = COOKIES_PATH) -> None:
        if not self.driver:
            return
        try:
            path.write_text(json.dumps(self.driver.get_cookies(), indent=2))
            self.log.debug("Cookies saved → %s", path)
        except Exception as exc:
            self.log.debug("Cookie save failed: %s", exc)

    def load_cookies(self, path: Path = COOKIES_PATH) -> bool:
        if not self.driver or not path.exists():
            return False
        try:
            cookies: list[dict] = json.loads(path.read_text())
            for cookie in cookies:
                try:
                    self.driver.add_cookie(cookie)
                except Exception:
                    pass  # stale/expired cookies are ignored
            self.log.debug("Cookies loaded ← %s", path)
            return True
        except Exception as exc:
            self.log.debug("Cookie load failed: %s", exc)
            return False


# ─── Facebook Auth ────────────────────────────────────────────────────────────

class FacebookAuth:
    """Handles logging in to Facebook and detecting authenticated state."""

    def __init__(self, browser: Browser, log: logging.Logger):
        self.browser = browser
        self.log = log

    @property
    def driver(self):
        return self.browser.driver

    def is_logged_in(self) -> bool:
        """True if the current browser session is authenticated."""
        self.driver.get(FB_BASE + "/")
        _pause(3, 5)
        url = self.driver.current_url
        if "login" in url or "checkpoint" in url:
            return False
        # Look for elements that only exist when logged in
        for selector in (
            "//div[@data-pagelet='NavBar']",
            "//a[@aria-label='Home']",
            "//div[@aria-label='Facebook']",
        ):
            try:
                self.driver.find_element(By.XPATH, selector)
                return True
            except NoSuchElementException:
                pass
        return False

    def try_cookie_login(self) -> bool:
        """Attempt to restore a previous session from saved cookies."""
        # Navigate first so add_cookie applies to the right domain
        self.driver.get(FB_BASE + "/")
        _pause(2, 3)
        if self.browser.load_cookies():
            self.driver.refresh()
            _pause(3, 5)
            if self.is_logged_in():
                self.log.info("Logged in via saved cookies — skipping password prompt.")
                return True
        return False

    def login(self, email: str, password: str) -> bool:
        """Log in with email + password. Handles 2FA checkpoints interactively."""
        self.log.info("Opening Facebook login page…")
        self.driver.get(FB_LOGIN_URL)
        _pause(3, 5)

        try:
            # ── Locate email field ────────────────────────────────────────────
            # Try a cascade of selectors from most to least specific so that
            # minor Facebook DOM changes don't break the whole flow.
            email_field = self._find_first(
                30,
                (By.ID,    "email"),
                (By.NAME,  "email"),
                (By.XPATH, "//input[@placeholder='Email or mobile number']"),
                (By.XPATH, "//input[@type='email']"),
                (By.XPATH, "//input[@type='text' and contains(@aria-label,'email') or contains(@aria-label,'Email')]"),
                (By.XPATH, "(//input[@type='text'])[1]"),
            )
            if email_field is None:
                self.log.error(
                    "Email input not found. The page loaded as:\n  %s\n"
                    "Try running without --headless so you can see what Facebook is showing.",
                    self.driver.current_url,
                )
                return False

            email_field.click()
            _pause(0.3, 0.7)
            _human_type(email_field, email)
            _pause(0.6, 1.3)

            # ── Locate password field ─────────────────────────────────────────
            pass_field = self._find_first(
                10,
                (By.ID,    "pass"),
                (By.NAME,  "pass"),
                (By.XPATH, "//input[@placeholder='Password']"),
                (By.XPATH, "//input[@type='password']"),
            )
            if pass_field is None:
                self.log.error("Password input not found.")
                return False

            pass_field.click()
            _pause(0.3, 0.7)
            _human_type(pass_field, password)
            _pause(0.6, 1.3)

            # ── Click Login button ────────────────────────────────────────────
            login_btn = self._find_first(
                10,
                (By.NAME,  "login"),
                (By.XPATH, "//button[@type='submit']"),
                (By.XPATH, "//button[normalize-space()='Log in']"),
                (By.XPATH, "//div[@aria-label='Log in']"),
                (By.XPATH, "//input[@type='submit']"),
            )
            if login_btn:
                login_btn.click()
            else:
                # Last resort: submit the form via Enter key
                self.log.debug("Login button not found — submitting via Enter key.")
                pass_field.send_keys(Keys.RETURN)

            _pause(5, 9)

            # ── Handle 2FA / checkpoint ───────────────────────────────────────
            if "checkpoint" in self.driver.current_url or "two_step" in self.driver.current_url:
                self.log.warning(
                    "\n*** Facebook is requesting additional verification. ***\n"
                    "Complete the check in the browser window, then press Enter here."
                )
                input("Press Enter once verification is complete > ")
                _pause(3, 5)

            if self.is_logged_in():
                self.log.info("Login successful.")
                self.browser.save_cookies()
                return True

            self.log.error(
                "Login did not succeed — check credentials or handle any CAPTCHA manually.\n"
                "Current URL: %s",
                self.driver.current_url,
            )
            return False

        except Exception as exc:
            self.log.error("Unexpected error during login: %s", exc, exc_info=True)
            return False

    def _find_first(self, timeout: int, *locators: tuple) -> object | None:
        """
        Try each (By, value) locator in order, waiting up to `timeout` seconds
        for the first one. Returns the element or None if none matched.
        """
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            for locator in locators:
                try:
                    el = self.driver.find_element(*locator)
                    if el.is_displayed():
                        return el
                except NoSuchElementException:
                    pass
            time.sleep(0.5)
        return None


# ─── Marketplace Parser ───────────────────────────────────────────────────────

class MarketplaceParser:
    """Extracts Listing objects from a loaded Marketplace search results page."""

    # Matches dollar prices like "$1,200" or "$35.00"
    _PRICE_RE = re.compile(r"\$\s*([\d,]+(?:\.\d{1,2})?)")
    # Extracts the numeric listing ID from a marketplace item URL
    _ID_RE = re.compile(r"/marketplace/item/(\d+)")

    def __init__(self, driver, log: logging.Logger):
        self.driver = driver
        self.log = log

    # ── Public API ────────────────────────────────────────────────────────────

    def parse_listings(self) -> list[Listing]:
        """Scroll the page and extract all visible listings."""
        self._scroll_to_load()
        listings: list[Listing] = []
        seen_in_pass: set[str] = set()

        try:
            # FB renders each listing card as an <a> linking to /marketplace/item/ID/
            link_els = self.driver.find_elements(
                By.XPATH, "//a[contains(@href, '/marketplace/item/')]"
            )
        except WebDriverException as exc:
            self.log.warning("Could not find listing elements: %s", exc)
            return listings

        for el in link_els:
            try:
                href = el.get_attribute("href") or ""
                m = self._ID_RE.search(href)
                if not m:
                    continue
                listing_id = m.group(1)
                if listing_id in seen_in_pass:
                    continue
                seen_in_pass.add(listing_id)

                clean_url = f"{FB_BASE}/marketplace/item/{listing_id}/"

                # aria-label is the most reliable data source; fall back to child spans
                aria = el.get_attribute("aria-label") or ""
                title, price, location = self._parse_aria_label(aria)

                if not title:
                    title, price = self._scrape_child_spans(el)
                if not title:
                    continue

                listings.append(Listing(
                    listing_id=listing_id,
                    title=title,
                    price=price,
                    url=clean_url,
                    location=location,
                ))

            except StaleElementReferenceException:
                continue  # element disappeared mid-iteration; safe to skip
            except Exception as exc:
                self.log.debug("Skipping element due to parse error: %s", exc)

        self.log.info("Parsed %d unique listings.", len(listings))
        return listings

    # ── Helpers ───────────────────────────────────────────────────────────────

    def _scroll_to_load(self, steps: int = 4) -> None:
        """Scroll down incrementally to trigger lazy-loading of listing cards."""
        for _ in range(steps):
            self.driver.execute_script("window.scrollBy(0, 700);")
            _pause(0.7, 1.4)
        self.driver.execute_script("window.scrollTo(0, 0);")
        _pause(0.5, 1.0)

    def _extract_price(self, text: str) -> float | None:
        if not text:
            return None
        if "free" in text.lower():
            return 0.0
        m = self._PRICE_RE.search(text)
        return float(m.group(1).replace(",", "")) if m else None

    def _parse_aria_label(self, aria: str) -> tuple[str, float | None, str]:
        """
        Facebook's aria-labels on listing cards loosely follow:
            "TITLE, $PRICE. LOCATION"
        Returns (title, price, location). Any part may be empty/None.
        """
        if not aria:
            return "", None, ""

        dot_parts = aria.split(".", 1)
        first = dot_parts[0]
        location = dot_parts[1].strip() if len(dot_parts) > 1 else ""

        comma_parts = first.split(",", 1)
        title = comma_parts[0].strip()
        price_text = comma_parts[1].strip() if len(comma_parts) > 1 else ""
        price = self._extract_price(price_text) or self._extract_price(first)

        return title, price, location

    def _scrape_child_spans(self, el) -> tuple[str, float | None]:
        """
        Fallback parser: scan visible <span> text nodes inside the card element.
        Heuristic: the first non-price, non-trivial span is the title.
        """
        try:
            spans = el.find_elements(By.TAG_NAME, "span")
            texts = [s.text.strip() for s in spans if s.text.strip()]
        except Exception:
            return "", None

        title = ""
        price: float | None = None

        for text in texts:
            p = self._extract_price(text)
            if p is not None and price is None:
                price = p
            elif not title and len(text) > 3 and not text.startswith("$"):
                title = text

        return title, price


# ─── Monitor (main loop) ──────────────────────────────────────────────────────

class Monitor:
    """Ties all components together and runs the continuous monitoring loop."""

    def __init__(
        self,
        configs: list[SearchConfig],
        scan_interval: int,
        fb_email: str,
        fb_password: str,
        headless: bool = False,
        verbose: bool = False,
    ):
        self.configs = configs                        # one or more active queries
        self.scan_interval = max(30, scan_interval)  # global cycle interval (floor 30 s)
        self.fb_email = fb_email
        self.fb_password = fb_password
        self.log = setup_logging(verbose)
        self.stop_event = Event()
        self.browser = Browser(headless=headless, log=self.log)
        self.seen = SeenTracker()           # shared across all queries in this session
        self.notifier = Notifier(self.log)  # config-agnostic; config passed per notify()

    def run(self) -> None:
        self._register_signals()
        self._print_banner()

        self.browser.start()
        auth = FacebookAuth(self.browser, self.log)

        if not auth.try_cookie_login():
            if not self.fb_email or not self.fb_password:
                self.log.error(
                    "No saved session found and no credentials supplied.\n"
                    "Provide --email and --password, or run interactively."
                )
                self.browser.quit()
                return
            if not auth.login(self.fb_email, self.fb_password):
                self.browser.quit()
                return

        # One parser instance is reused across all queries and all cycles.
        parser = MarketplaceParser(self.browser.driver, self.log)
        cycle_n = 0

        while not self.stop_event.is_set():
            cycle_n += 1
            self.log.info(
                "─── Cycle #%d  (%s) — %d quer%s ───",
                cycle_n,
                datetime.now().strftime("%H:%M:%S"),
                len(self.configs),
                "y" if len(self.configs) == 1 else "ies",
            )

            for i, config in enumerate(self.configs, start=1):
                if self.stop_event.is_set():
                    break

                search_url = config.build_search_url()
                self.log.info(
                    "  [%d/%d] '%s'  %s",
                    i, len(self.configs), config.keyword, search_url,
                )

                try:
                    self.browser.driver.get(search_url)

                    # Wait up to 20 s for at least one listing card to appear
                    try:
                        WebDriverWait(self.browser.driver, 20).until(
                            EC.presence_of_element_located(
                                (By.XPATH, "//a[contains(@href, '/marketplace/item/')]")
                            )
                        )
                    except TimeoutException:
                        self.log.warning(
                            "  [%s] No listing cards within 20 s — "
                            "page may be empty, rate-limited, or login expired.",
                            config.keyword,
                        )
                        continue

                    listings = parser.parse_listings()
                    new_matches = 0

                    for listing in listings:
                        if not self.seen.is_new(listing.listing_id):
                            continue
                        # Mark seen BEFORE the match check so a listing that appears
                        # in multiple queries' results is only alerted once
                        # (for whichever query evaluates it first this cycle).
                        self.seen.mark_seen(listing.listing_id)
                        if config.matches(listing):
                            new_matches += 1
                            self.notifier.notify(listing, config)

                    if new_matches == 0:
                        self.log.info("  [%s] No new matches.", config.keyword)

                except WebDriverException as exc:
                    self.log.warning("Browser error on '%s': %s", config.keyword, exc)
                    if self._looks_like_crash(str(exc)):
                        self._restart_browser(auth, parser)
                        break  # abort remaining queries; outer loop will restart cycle

                except Exception as exc:
                    self.log.error(
                        "Unexpected error on '%s': %s", config.keyword, exc, exc_info=True
                    )

                # Courtesy pause between queries (skipped after the last one)
                if i < len(self.configs) and not self.stop_event.is_set():
                    _pause(2, 5)

            # End of cycle — wait the global interval (±15 s jitter)
            if not self.stop_event.is_set():
                wait = max(30, self.scan_interval + random.uniform(-15, 15))
                self.log.info("Cycle complete. Next in %.0f s…", wait)
                self.stop_event.wait(timeout=wait)

        self.browser.quit()
        self.log.info("Monitor stopped cleanly.")

    # ── Internal helpers ──────────────────────────────────────────────────────

    def _register_signals(self) -> None:
        def _handler(sig, frame):
            self.log.info("Interrupt received — shutting down…")
            self.stop_event.set()
        signal.signal(signal.SIGINT, _handler)
        signal.signal(signal.SIGTERM, _handler)

    def _print_banner(self) -> None:
        self.log.info("=" * 62)
        self.log.info(" Facebook Marketplace Monitor  v%s", VERSION)
        self.log.info("=" * 62)
        self.log.info(" Active queries (%d):", len(self.configs))
        for i, cfg in enumerate(self.configs, start=1):
            lo = f"${cfg.min_price:,.0f}" if cfg.min_price is not None else "any"
            hi = f"${cfg.max_price:,.0f}" if cfg.max_price is not None else "any"
            ch = ", ".join(filter(None, [
                "Discord" if cfg.discord_webhook else "",
                "email"   if cfg.email_config    else "",
            ])) or "console"
            self.log.info("   %d. %-24s  $%s – $%s  [%s]", i, cfg.keyword, lo, hi, ch)
        self.log.info(" Cycle interval : %d s", self.scan_interval)
        desktop_note = ", desktop" if HAS_PLYER else ""
        self.log.info(" Always sent    : console%s", desktop_note)
        self.log.info("=" * 62)
        self.log.info(" Press Ctrl+C to stop.")
        self.log.info("=" * 62)

    @staticmethod
    def _looks_like_crash(msg: str) -> bool:
        return any(word in msg.lower() for word in ("session", "chrome", "no such window"))

    def _restart_browser(self, auth: FacebookAuth, parser: MarketplaceParser) -> None:
        self.log.info("Restarting browser after crash…")
        self.browser.quit()
        _pause(5, 10)
        self.browser.start()
        parser.driver = self.browser.driver
        if not auth.try_cookie_login():
            auth.login(self.fb_email, self.fb_password)


# ─── Utility functions ────────────────────────────────────────────────────────

def _pause(min_s: float = 1.0, max_s: float = 3.0) -> None:
    """Sleep for a random interval to mimic human pacing and respect rate limits."""
    time.sleep(random.uniform(min_s, max_s))


def _human_type(element, text: str) -> None:
    """Type text character-by-character with randomised inter-key delays."""
    for ch in text:
        element.send_keys(ch)
        time.sleep(random.uniform(0.04, 0.18))


# ─── Credential helpers ───────────────────────────────────────────────────────

def _load_dotenv(path: Path = ENV_PATH) -> dict[str, str]:
    """Parse a .env file and return {KEY: value}. Ignores comments and blanks."""
    if not path.exists():
        return {}
    result: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, _, val = line.partition("=")
        result[key.strip()] = val.strip()
    return result


def _save_dotenv(updates: dict[str, str], path: Path = ENV_PATH) -> None:
    """
    Merge `updates` into `path`, preserving existing lines and comments.
    Keys already present are updated in-place; new keys are appended.
    """
    lines: list[str] = []
    key_to_idx: dict[str, int] = {}

    if path.exists():
        for line in path.read_text(encoding="utf-8").splitlines():
            stripped = line.strip()
            if stripped and not stripped.startswith("#") and "=" in stripped:
                key, _, _ = stripped.partition("=")
                key_to_idx[key.strip()] = len(lines)
            lines.append(line)

    for key, val in updates.items():
        if key in key_to_idx:
            lines[key_to_idx[key]] = f"{key}={val}"
        else:
            lines.append(f"{key}={val}")

    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _resolve_credentials(
    cli_email: str | None,
    cli_password: str | None,
) -> tuple[str, str]:
    """
    Resolve Facebook credentials through a priority chain:
      1. --email / --password CLI flags
      2. .env file    (FBM_EMAIL / FBM_PASSWORD)
      3. OS env vars  (FBM_EMAIL / FBM_PASSWORD)
      4. Interactive prompt  →  offers to save to .env so future runs skip this step

    Returns (email, password).
    """
    env_file = _load_dotenv()

    email = (
        cli_email
        or env_file.get("FBM_EMAIL")
        or os.environ.get("FBM_EMAIL", "")
    )
    password = (
        cli_password
        or env_file.get("FBM_PASSWORD")
        or os.environ.get("FBM_PASSWORD", "")
    )

    prompted = False
    if not email:
        print("Facebook Login")
        print("  (Tip: save credentials to .env so you're not prompted each time.)")
        email = input("Facebook email   : ").strip()
        prompted = True
    if not password:
        if not prompted:
            print("Facebook Login")
        password = getpass.getpass("Facebook password: ")
        prompted = True

    # Offer to persist if the user had to type anything
    if prompted and email and password:
        ans = input("Save credentials to .env for future runs? [y/N]: ").strip().lower()
        if ans == "y":
            _save_dotenv({"FBM_EMAIL": email, "FBM_PASSWORD": password})
            print(f"  Saved → {ENV_PATH}")
            print("  ⚠  .env stores your password in plain text.")
            print("     Keep it private and add it to .gitignore.")

    return email, password


# ─── Interactive setup wizard ─────────────────────────────────────────────────

def _wizard() -> tuple[list[SearchConfig], int, str, str]:
    """
    Interactive setup wizard.  Supports adding multiple search queries in one
    session.  Returns (configs, scan_interval, fb_email, fb_password).
    """
    print()
    print("=" * 62)
    print("  Facebook Marketplace Monitor — Interactive Setup")
    print("=" * 62)
    print()

    def ask(prompt: str, required: bool = False) -> str:
        while True:
            val = input(prompt).strip()
            if val or not required:
                return val
            print("  (This field is required.)")

    configs: list[SearchConfig] = []

    while True:
        if configs:
            print(f"\n─── Query #{len(configs) + 1} ───")

        keyword   = ask("Search keyword  (e.g. 'iPhone 14 Pro'): ", required=True)
        raw_min   = ask("Minimum price   (leave blank for none): ")
        raw_max   = ask("Maximum price   (leave blank for none): ")
        raw_extra = ask("Extra keywords  (comma-separated, optional): ")
        raw_rad   = ask("Search radius   (miles, optional): ")
        discord   = ask("Discord webhook (optional, leave blank to skip): ")

        configs.append(SearchConfig(
            keyword=keyword,
            min_price=float(raw_min) if raw_min else None,
            max_price=float(raw_max) if raw_max else None,
            extra_keywords=[k.strip() for k in raw_extra.split(",") if k.strip()],
            radius=int(raw_rad) if raw_rad else None,
            scan_interval=DEFAULT_SCAN_INTERVAL,  # placeholder; global interval overrides
            discord_webhook=discord or None,
        ))
        print(f"  ✓ Query {len(configs)} added: '{keyword}'")

        if input("\nAdd another query? [y/N]: ").strip().lower() != "y":
            break

    # Global cycle interval — asked once after all queries are collected
    print()
    raw_interval = ask(f"Scan cycle interval in seconds (default {DEFAULT_SCAN_INTERVAL}): ")
    scan_interval = int(raw_interval) if raw_interval else DEFAULT_SCAN_INTERVAL

    # Offer to save — use the new multi-query format if more than one query
    print()
    if len(configs) == 1:
        if input("Save this query for future runs? [y/N]: ").strip().lower() == "y":
            configs[0].scan_interval = scan_interval
            configs[0].save()
            print(f"  Saved → {CONFIG_PATH}")
    else:
        if input(f"Save all {len(configs)} queries for future runs? [y/N]: ").strip().lower() == "y":
            SearchConfig.save_queries(configs, scan_interval)
            print(f"  Saved → {QUERIES_PATH}")

    print()
    fb_email, fb_pass = _resolve_credentials(None, None)

    return configs, scan_interval, fb_email, fb_pass


# ─── Argument parser ──────────────────────────────────────────────────────────

def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="fbm_monitor.py",
        description="Alert you when Facebook Marketplace listings match your criteria.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    p.add_argument("--keyword",          "-k", help="Primary search term (single query)")
    p.add_argument("--min-price",        type=float, help="Minimum price")
    p.add_argument("--max-price",        type=float, help="Maximum price")
    p.add_argument("--extra-keywords",   nargs="+", metavar="KW",
                   help="Additional words that must appear in the listing title")
    p.add_argument("--radius",           type=int, help="Search radius in miles")
    p.add_argument("--interval",         type=int, default=DEFAULT_SCAN_INTERVAL,
                   help=f"Seconds between scan cycles (default: {DEFAULT_SCAN_INTERVAL})")
    p.add_argument("--discord-webhook",  help="Discord webhook URL for rich alerts")
    p.add_argument("--email",            help="Facebook account email")
    p.add_argument("--password",         help="Facebook password (caution: visible in shell history)")
    p.add_argument("--queries",          type=Path, metavar="FILE",
                   help="JSON file containing multiple queries (fbm_queries.json format)")
    p.add_argument("--config",           type=Path,
                   help="Single-query JSON file (backward-compat; use --queries for multiple)")
    p.add_argument("--no-headless",         action="store_false",
                   help="Run Chrome with a visible window (may be detected more easily)")
    p.add_argument("--verbose",          action="store_true", help="Enable debug logging")
    return p


# ─── Entry point ──────────────────────────────────────────────────────────────

def main() -> None:
    args = _build_parser().parse_args()

    configs: list[SearchConfig]
    scan_interval: int
    fb_email: str = ""
    fb_pass:  str = ""
    creds_resolved = False   # True when wizard already resolved credentials

    # ── Resolution order (queries) ────────────────────────────────────────────
    # 1. --queries FILE       explicit multi-query file
    # 2. --config FILE        explicit single-query file (backward-compat)
    # 3. --keyword ...        single query from CLI flags
    # 4. fbm_queries.json     auto-detected multi-query file in CWD
    # 5. fbm_config.json      auto-detected single-query file in CWD (legacy)
    # 6. interactive wizard   prompts for queries AND credentials together

    if args.queries:
        if not args.queries.exists():
            print(f"ERROR: Queries file not found: {args.queries}")
            sys.exit(1)
        print(f"Loading queries from {args.queries}")
        configs, scan_interval = SearchConfig.load_queries(args.queries)

    elif args.config:
        if not args.config.exists():
            print(f"ERROR: Config file not found: {args.config}")
            sys.exit(1)
        single = SearchConfig.load(args.config)
        configs, scan_interval = [single], single.scan_interval

    elif args.keyword:
        single = SearchConfig(
            keyword=args.keyword,
            min_price=args.min_price,
            max_price=args.max_price,
            extra_keywords=args.extra_keywords or [],
            radius=args.radius,
            scan_interval=args.interval,
            discord_webhook=args.discord_webhook,
        )
        configs, scan_interval = [single], args.interval

    elif QUERIES_PATH.exists():
        print(f"Loading saved queries from {QUERIES_PATH}")
        configs, scan_interval = SearchConfig.load_queries(QUERIES_PATH)

    elif CONFIG_PATH.exists():
        print(f"Loading saved config from {CONFIG_PATH}")
        single = SearchConfig.load(CONFIG_PATH)
        configs, scan_interval = [single], single.scan_interval

    else:
        # Wizard collects both queries and credentials in one flow
        configs, scan_interval, fb_email, fb_pass = _wizard()
        creds_resolved = True

    # ── Credentials (skipped when wizard already handled them) ────────────────
    # Priority: --email/--password flags → .env → FBM_EMAIL/FBM_PASSWORD env
    # vars → interactive prompt (offers to save to .env on first use).
    if not creds_resolved:
        fb_email, fb_pass = _resolve_credentials(args.email, args.password)

    # ── Validate ──────────────────────────────────────────────────────────────

    if not configs:
        print("ERROR: No search queries configured.")
        sys.exit(1)
    for cfg in configs:
        if not cfg.keyword:
            print("ERROR: Every query must have a keyword.")
            sys.exit(1)

    # ── Start monitoring ──────────────────────────────────────────────────────

    Monitor(
        configs=configs,
        scan_interval=scan_interval,
        fb_email=fb_email,
        fb_password=fb_pass,
        headless=args.no_headless,
        verbose=args.verbose,
    ).run()


if __name__ == "__main__":
    main()
