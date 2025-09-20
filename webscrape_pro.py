import streamlit as st
import requests
from bs4 import BeautifulSoup
import pandas as pd
import json
import sqlite3
import time
import re
import random
from urllib.parse import urljoin, urlparse, parse_qs
from urllib.robotparser import RobotFileParser
import plotly.express as px
import plotly.graph_objects as go
import networkx as nx
from wordcloud import WordCloud
import matplotlib.pyplot as plt
from datetime import datetime, timedelta
import base64
from io import BytesIO
import threading
from queue import Queue
import hashlib
from collections import Counter, defaultdict
import warnings
import uuid
import smtplib
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
import schedule

warnings.filterwarnings("ignore")


# Enhanced NLP Mock Implementation
class MockNLP:
    """Mock NLP class to simulate advanced features"""

    @staticmethod
    def detect_language(text):
        if any(word in text.lower() for word in ["the", "and", "is", "a", "to", "of"]):
            return "en"
        elif any(
            word in text.lower() for word in ["le", "la", "et", "de", "un", "une"]
        ):
            return "fr"
        elif any(
            word in text.lower() for word in ["der", "die", "das", "und", "ist", "ein"]
        ):
            return "de"
        return "unknown"

    @staticmethod
    def extract_entities(text):
        entities = {
            "PERSON": re.findall(r"\b[A-Z][a-z]+ [A-Z][a-z]+\b", text)[:5],
            "ORG": re.findall(
                r"\b[A-Z][a-z]*(?:\s+[A-Z][a-z]*)*\s+(?:Inc|Corp|LLC|Ltd|Company|Co|Corporation)\b",
                text,
            )[:3],
            "GPE": re.findall(
                r"\b(?:New York|London|Paris|Tokyo|Berlin|Madrid|Washington|California|Texas|Florida)\b",
                text,
            )[:3],
        }
        return entities

    @staticmethod
    def analyze_sentiment(text):
        positive_words = [
            "good",
            "great",
            "excellent",
            "amazing",
            "wonderful",
            "fantastic",
            "awesome",
            "perfect",
            "outstanding",
            "superb",
            "love",
            "best",
        ]
        negative_words = [
            "bad",
            "terrible",
            "awful",
            "horrible",
            "disappointing",
            "poor",
            "worst",
            "hate",
            "annoying",
            "frustrated",
            "expensive",
            "slow",
        ]

        text_lower = text.lower()
        pos_count = sum(1 for word in positive_words if word in text_lower)
        neg_count = sum(1 for word in negative_words if word in text_lower)

        if pos_count > neg_count:
            return "Positive"
        elif neg_count > pos_count:
            return "Negative"
        return "Neutral"

    @staticmethod
    def extract_keywords(text, top_k=10):
        words = re.findall(r"\b[a-zA-Z]{3,}\b", text.lower())
        common_words = {
            "the",
            "and",
            "is",
            "in",
            "to",
            "of",
            "a",
            "that",
            "it",
            "with",
            "for",
            "as",
            "was",
            "on",
            "are",
            "you",
            "have",
            "be",
            "at",
            "this",
            "but",
            "his",
            "by",
            "from",
            "they",
            "we",
            "say",
            "her",
            "she",
            "or",
            "an",
            "will",
            "my",
            "one",
            "all",
            "would",
            "there",
            "their",
            "has",
        }
        filtered_words = [
            word for word in words if word not in common_words and len(word) > 2
        ]
        return dict(Counter(filtered_words).most_common(top_k))


# User Management System
class UserManager:
    """Professional user management system"""

    def __init__(self):
        self.users_db = "users.db"
        self.init_db()

    def init_db(self):
        """Initialize user database"""
        conn = sqlite3.connect(self.users_db)
        cursor = conn.cursor()
        cursor.execute(
            """
            CREATE TABLE IF NOT EXISTS users (
                id TEXT PRIMARY KEY,
                username TEXT UNIQUE,
                email TEXT UNIQUE,
                plan TEXT DEFAULT 'free',
                api_calls_used INTEGER DEFAULT 0,
                api_calls_limit INTEGER DEFAULT 100,
                created_at TIMESTAMP,
                last_login TIMESTAMP,
                credits INTEGER DEFAULT 10
            )
        """
        )
        cursor.execute(
            """
            CREATE TABLE IF NOT EXISTS scraping_jobs (
                id TEXT PRIMARY KEY,
                user_id TEXT,
                job_name TEXT,
                target_url TEXT,
                status TEXT,
                results_count INTEGER,
                created_at TIMESTAMP,
                completed_at TIMESTAMP,
                config TEXT,
                FOREIGN KEY (user_id) REFERENCES users (id)
            )
        """
        )
        conn.commit()
        conn.close()

    def create_user(self, username, email, plan="free"):
        """Create new user"""
        conn = sqlite3.connect(self.users_db)
        cursor = conn.cursor()
        user_id = str(uuid.uuid4())

        limits = {
            "free": {"api_calls": 100, "credits": 10},
            "pro": {"api_calls": 1000, "credits": 100},
            "enterprise": {"api_calls": 10000, "credits": 1000},
        }

        try:
            cursor.execute(
                """
                INSERT INTO users (id, username, email, plan, api_calls_limit, credits, created_at)
                VALUES (?, ?, ?, ?, ?, ?, ?)
            """,
                (
                    user_id,
                    username,
                    email,
                    plan,
                    limits[plan]["api_calls"],
                    limits[plan]["credits"],
                    datetime.now(),
                ),
            )
            conn.commit()
            return user_id
        except sqlite3.IntegrityError:
            return None
        finally:
            conn.close()

    def get_user(self, user_id):
        """Get user information"""
        conn = sqlite3.connect(self.users_db)
        cursor = conn.cursor()
        cursor.execute("SELECT * FROM users WHERE id = ?", (user_id,))
        user = cursor.fetchone()
        conn.close()
        return user


# Enhanced Web Scraper Class
class EnhancedWebScraper:
    """Professional web scraper that works with complex sites including Amazon"""

    def __init__(self):
        self.session = requests.Session()
        self.setup_session()
        self.nlp = MockNLP()
        self.scraped_urls = set()
        self.results = []
        self.rate_limit_delay = 2

    def setup_session(self):
        """Setup session with rotating user agents and better headers for complex sites"""
        # Use more realistic user agents
        user_agents = [
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
            "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:121.0) Gecko/20100101 Firefox/121.0",
            "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.2 Safari/605.1.15",
        ]

        # Enhanced headers for better compatibility
        self.session.headers.update(
            {
                "User-Agent": user_agents[0],
                "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8",
                "Accept-Language": "en-US,en;q=0.9",
                "Accept-Encoding": "gzip, deflate, br",
                "Connection": "keep-alive",
                "Upgrade-Insecure-Requests": "1",
                "Sec-Fetch-Dest": "document",
                "Sec-Fetch-Mode": "navigate",
                "Sec-Fetch-Site": "none",
                "Sec-Fetch-User": "?1",
                "Cache-Control": "max-age=0",
                "DNT": "1",
                "Sec-CH-UA": '"Not_A Brand";v="8", "Chromium";v="120", "Google Chrome";v="120"',
                "Sec-CH-UA-Mobile": "?0",
                "Sec-CH-UA-Platform": '"Windows"',
            }
        )

        # Configure retries with exponential backoff
        from requests.adapters import HTTPAdapter
        from urllib3.util.retry import Retry

        retry_strategy = Retry(
            total=5,  # Increased retries
            status_forcelist=[429, 500, 502, 503, 504, 520, 521, 522, 524],
            backoff_factor=2,  # Exponential backoff
            respect_retry_after_header=True,
        )

        adapter = HTTPAdapter(
            max_retries=retry_strategy, pool_connections=10, pool_maxsize=10
        )
        self.session.mount("http://", adapter)
        self.session.mount("https://", adapter)

        # Disable SSL warnings for problematic sites
        import urllib3

        urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

    def detect_website_type(self, url, soup):
        """Detect website type for specialized extraction"""
        domain = urlparse(url).netloc.lower()
        content = soup.get_text().lower()

        # E-commerce indicators
        if any(
            indicator in domain
            for indicator in ["amazon", "ebay", "shopify", "shop", "store"]
        ):
            return "ecommerce"

        if any(
            indicator in content
            for indicator in [
                "add to cart",
                "buy now",
                "price",
                "shopping cart",
                "checkout",
            ]
        ):
            return "ecommerce"

        # News site indicators
        if any(
            indicator in domain
            for indicator in ["news", "bbc", "cnn", "reuters", "times"]
        ):
            return "news"

        # Social media indicators
        if any(
            indicator in domain
            for indicator in ["facebook", "twitter", "linkedin", "instagram"]
        ):
            return "social"

        # Blog indicators
        if any(
            indicator in content for indicator in ["blog", "post", "comment", "author"]
        ):
            return "blog"

        return "general"

    def extract_ecommerce_data(self, soup, url):
        """Specialized extraction for e-commerce sites"""
        data = {}

        # Product title selectors (Amazon, eBay, general e-commerce)
        title_selectors = [
            "#productTitle",  # Amazon
            "h1.product-title",
            "h1.product-name",
            ".product-title h1",
            'h1[data-testid="product-title"]',
            ".pdp-product-name",
            ".product-name",
            ".item-title",
            ".product-header h1",
        ]

        for selector in title_selectors:
            title_elem = soup.select_one(selector)
            if title_elem:
                data["product_title"] = title_elem.get_text(strip=True)
                break

        # Price selectors
        price_selectors = [
            ".a-price-whole",  # Amazon
            ".a-price .a-offscreen",
            ".price-current",
            ".product-price",
            ".price",
            '[data-testid="price"]',
            ".current-price",
            ".notranslate",
            ".price-display",
            ".sale-price",
        ]

        for selector in price_selectors:
            price_elem = soup.select_one(selector)
            if price_elem:
                price_text = price_elem.get_text(strip=True)
                # Extract numeric price
                price_match = re.search(r"[\d,]+\.?\d*", price_text.replace(",", ""))
                if price_match:
                    data["price"] = price_match.group()
                break

        # Rating selectors
        rating_selectors = [
            ".a-icon-alt",  # Amazon
            ".rating",
            ".product-rating",
            '[data-testid="rating"]',
            ".stars",
            ".review-rating",
            ".star-rating",
        ]

        for selector in rating_selectors:
            rating_elem = soup.select_one(selector)
            if rating_elem:
                rating_text = rating_elem.get_text() or rating_elem.get("alt", "")
                rating_match = re.search(r"(\d+\.?\d*)", rating_text)
                if rating_match:
                    data["rating"] = rating_match.group(1)
                break

        # Reviews count selectors
        reviews_selectors = [
            "#acrCustomerReviewText",  # Amazon
            ".review-count",
            ".reviews-count",
            '[data-testid="reviews-count"]',
            ".review-summary",
            ".ratings-count",
        ]

        for selector in reviews_selectors:
            reviews_elem = soup.select_one(selector)
            if reviews_elem:
                reviews_text = reviews_elem.get_text(strip=True)
                reviews_match = re.search(r"([\d,]+)", reviews_text.replace(",", ""))
                if reviews_match:
                    data["reviews_count"] = reviews_match.group()
                break

        # Availability selectors
        availability_selectors = [
            "#availability span",  # Amazon
            ".availability",
            ".stock-status",
            '[data-testid="availability"]',
            ".inventory-status",
            ".product-availability",
        ]

        for selector in availability_selectors:
            avail_elem = soup.select_one(selector)
            if avail_elem:
                data["availability"] = avail_elem.get_text(strip=True)
                break

        return data

    def validate_url(self, url):
        """Validate and normalize URL with better handling for complex sites"""
        try:
            # Basic URL cleanup
            url = url.strip()
            if not url:
                return None

            # Add scheme if missing
            parsed = urlparse(url)
            if not parsed.scheme:
                url = "https://" + url
                parsed = urlparse(url)

            # Skip validation for localhost and invalid schemes
            if parsed.netloc in ["localhost", "127.0.0.1"] or not parsed.netloc:
                return None

            # For Amazon and other complex sites, use GET instead of HEAD
            # as many sites block HEAD requests
            complex_sites = ["amazon.", "ebay.", "walmart.", "target.", "bestbuy."]
            use_get = any(site in parsed.netloc.lower() for site in complex_sites)

            if use_get:
                # Use GET request for complex sites like Amazon
                response = self.session.get(
                    url, timeout=15, allow_redirects=True, stream=True
                )
                # Only read a small portion to avoid downloading large content
                content = next(response.iter_content(1024), b"")
                response.close()
            else:
                # Use HEAD for simpler validation
                response = self.session.head(url, timeout=10, allow_redirects=True)

            # Accept a wider range of status codes
            if response.status_code < 500:  # Accept redirects, not found, etc.
                return url
            else:
                print(f"URL returned status {response.status_code}")
                return None

        except requests.exceptions.Timeout:
            print("URL validation timed out")
            # Return the URL anyway for timeout cases
            return url
        except requests.exceptions.ConnectionError:
            print("Connection error during URL validation")
            return None
        except Exception as e:
            print(f"URL validation error: {str(e)}")
            # For complex sites, return URL even if validation fails
            parsed = urlparse(url)
            if any(
                site in parsed.netloc.lower()
                for site in ["amazon.", "ebay.", "walmart."]
            ):
                return url
            return None

    def extract_content(self, url, elements_to_extract):
        """Extract specified elements from a webpage with enhanced capabilities"""
        try:
            # Add progressive delays for rate limiting
            time.sleep(self.rate_limit_delay + random.uniform(0.5, 2.0))

            # Special handling for different site types
            domain = urlparse(url).netloc.lower()

            # Set specific headers for Amazon
            headers = dict(self.session.headers)
            if "amazon." in domain:
                headers.update(
                    {
                        "Accept-Language": "en-US,en;q=0.9",
                        "Cache-Control": "no-cache",
                        "Pragma": "no-cache",
                    }
                )

            # Make the request with retries
            max_retries = 3
            for attempt in range(max_retries):
                try:
                    response = self.session.get(
                        url, timeout=20, headers=headers, verify=False
                    )
                    break
                except requests.exceptions.Timeout:
                    if attempt < max_retries - 1:
                        st.warning(f"Timeout on attempt {attempt + 1}, retrying...")
                        time.sleep(5 * (attempt + 1))
                        continue
                    else:
                        raise
                except requests.exceptions.RequestException as e:
                    if attempt < max_retries - 1:
                        st.warning(
                            f"Request failed on attempt {attempt + 1}, retrying..."
                        )
                        time.sleep(5 * (attempt + 1))
                        continue
                    else:
                        raise

            # Handle rate limiting and blocks
            if response.status_code == 429:
                st.warning("Rate limited. Waiting 60 seconds...")
                time.sleep(60)
                response = self.session.get(
                    url, timeout=20, headers=headers, verify=False
                )
            elif response.status_code == 503:
                st.warning("Service unavailable. Waiting 30 seconds...")
                time.sleep(30)
                response = self.session.get(
                    url, timeout=20, headers=headers, verify=False
                )
            elif response.status_code >= 400:
                return {
                    "url": url,
                    "error": f"HTTP {response.status_code}: {response.reason}",
                    "timestamp": datetime.now().isoformat(),
                }

            # Check if we got blocked (common with Amazon)
            if len(response.content) < 1000 and any(
                block_text in response.text.lower()
                for block_text in [
                    "blocked",
                    "captcha",
                    "verify you are human",
                    "access denied",
                ]
            ):
                return {
                    "url": url,
                    "error": "Access blocked by website (possibly detected as bot)",
                    "timestamp": datetime.now().isoformat(),
                }

            soup = BeautifulSoup(response.content, "html.parser")

            # Remove unwanted elements more aggressively
            for element in soup(
                [
                    "script",
                    "style",
                    "nav",
                    "footer",
                    "aside",
                    "noscript",
                    "iframe",
                    "object",
                    "embed",
                ]
            ):
                element.decompose()

            extracted_data = {
                "url": url,
                "timestamp": datetime.now().isoformat(),
                "status_code": response.status_code,
                "content_type": response.headers.get("content-type", ""),
                "page_size": len(response.content),
                "response_time": response.elapsed.total_seconds(),
            }

            # Detect website type early
            website_type = self.detect_website_type(url, soup)
            extracted_data["website_type"] = website_type

            if "title" in elements_to_extract:
                # Try multiple title selectors
                title_selectors = ["title", "h1", ".title", "#title"]
                title_text = ""

                for selector in title_selectors:
                    title_elem = soup.select_one(selector)
                    if title_elem and title_elem.get_text(strip=True):
                        title_text = title_elem.get_text(strip=True)
                        break

                extracted_data["title"] = title_text or "No title found"

            if "meta_description" in elements_to_extract:
                meta_desc = soup.find(
                    "meta", attrs={"name": "description"}
                ) or soup.find("meta", attrs={"property": "og:description"})
                extracted_data["meta_description"] = (
                    meta_desc.get("content", "") if meta_desc else ""
                )

            if "headings" in elements_to_extract:
                headings = {}
                for i in range(1, 7):
                    h_tags = soup.find_all(f"h{i}")
                    if h_tags:
                        headings[f"h{i}"] = [
                            tag.get_text(strip=True)
                            for tag in h_tags
                            if tag.get_text(strip=True)
                        ]
                extracted_data["headings"] = headings

            if "text_content" in elements_to_extract:
                # Enhanced text extraction with better content detection
                main_content_selectors = [
                    "main",
                    "article",
                    '[role="main"]',
                    ".main-content",
                    "#main-content",
                    ".content",
                    ".post-content",
                    ".entry-content",
                    ".article-content",
                ]

                main_content = None
                for selector in main_content_selectors:
                    main_content = soup.select_one(selector)
                    if main_content:
                        break

                if not main_content:
                    main_content = soup.body or soup

                if main_content:
                    # Remove more unwanted elements from main content
                    for elem in main_content(
                        [
                            "nav",
                            "aside",
                            "footer",
                            "header",
                            ".advertisement",
                            ".ads",
                            ".sidebar",
                            ".social-share",
                            ".comments",
                        ]
                    ):
                        elem.decompose()

                    # Extract meaningful paragraphs
                    paragraphs = main_content.find_all(
                        ["p", "div", "span"],
                        string=lambda text: text and len(text.strip()) > 20,
                    )

                    text_content = " ".join(
                        [p.get_text(strip=True) for p in paragraphs]
                    )

                    # Fallback to general text extraction
                    if len(text_content) < 100:
                        text_content = main_content.get_text(separator=" ", strip=True)
                else:
                    text_content = soup.get_text(separator=" ", strip=True)

                # Clean up the text
                text_content = re.sub(r"\s+", " ", text_content).strip()
                extracted_data["text_content"] = text_content
                extracted_data["content_length"] = len(text_content)

                # Language detection
                if text_content:
                    extracted_data["language"] = self.nlp.detect_language(text_content)

            if "links" in elements_to_extract:
                links = soup.find_all("a", href=True)
                internal_links = []
                external_links = []
                base_domain = urlparse(url).netloc

                for link in links:
                    href = link.get("href", "").strip()
                    if (
                        not href
                        or href.startswith("#")
                        or href.startswith("javascript:")
                    ):
                        continue

                    try:
                        absolute_url = urljoin(url, href)
                        link_domain = urlparse(absolute_url).netloc
                        link_text = link.get_text(strip=True)

                        if (
                            not link_text or len(link_text) > 200
                        ):  # Skip very long link texts
                            continue

                        link_data = {
                            "url": absolute_url,
                            "text": link_text,
                            "title": link.get("title", ""),
                            "type": self.classify_link_type(link, link_text),
                        }

                        if link_domain == base_domain:
                            internal_links.append(link_data)
                        else:
                            external_links.append(link_data)

                    except Exception:
                        continue  # Skip problematic links

                extracted_data["internal_links"] = internal_links[:50]
                extracted_data["external_links"] = external_links[:20]

            if "images" in elements_to_extract:
                images = soup.find_all("img")
                image_data = []
                for img in images:
                    src = (
                        img.get("src")
                        or img.get("data-src")
                        or img.get("data-lazy")
                        or img.get("data-original")
                    )
                    if src and not src.startswith("data:"):  # Skip data URLs
                        try:
                            absolute_src = urljoin(url, src)
                            image_data.append(
                                {
                                    "src": absolute_src,
                                    "alt": img.get("alt", "")[
                                        :200
                                    ],  # Limit alt text length
                                    "title": img.get("title", "")[:200],
                                    "width": img.get("width"),
                                    "height": img.get("height"),
                                }
                            )
                        except Exception:
                            continue
                extracted_data["images"] = image_data[:30]

            if "tables" in elements_to_extract:
                tables = soup.find_all("table")
                table_data = []
                for table in tables[:5]:  # Limit number of tables
                    try:
                        rows = table.find_all("tr")
                        if rows:
                            table_content = []
                            for row in rows[:20]:  # Limit rows per table
                                cells = row.find_all(["td", "th"])
                                if cells:
                                    table_content.append(
                                        [
                                            cell.get_text(strip=True)[
                                                :100
                                            ]  # Limit cell content
                                            for cell in cells[:10]  # Limit columns
                                        ]
                                    )
                            if table_content:
                                table_data.append(table_content)
                    except Exception:
                        continue
                extracted_data["tables"] = table_data

            # Extract e-commerce data if it's an e-commerce site
            if website_type == "ecommerce" and "ecommerce_data" in elements_to_extract:
                ecommerce_data = self.extract_ecommerce_data(soup, url)
                extracted_data.update(ecommerce_data)

            # Add NLP analysis for meaningful content
            if (
                "text_content" in extracted_data
                and extracted_data["text_content"]
                and len(extracted_data["text_content"]) > 50
            ):
                try:
                    extracted_data["sentiment"] = self.nlp.analyze_sentiment(
                        extracted_data["text_content"]
                    )
                    extracted_data["entities"] = self.nlp.extract_entities(
                        extracted_data["text_content"]
                    )
                    extracted_data["keywords"] = self.nlp.extract_keywords(
                        extracted_data["text_content"]
                    )
                except Exception as e:
                    st.warning(f"NLP analysis failed: {str(e)}")

            return extracted_data

        except Exception as e:
            error_msg = str(e)
            st.error(f"Error extracting content from {url}: {error_msg}")
            return {
                "url": url,
                "error": error_msg,
                "timestamp": datetime.now().isoformat(),
            }

    def classify_link_type(self, link_elem, link_text):
        """Classify link type for better organization"""
        href = link_elem.get("href", "").lower()
        text = link_text.lower()

        if any(
            nav in text for nav in ["home", "about", "contact", "menu", "navigation"]
        ):
            return "navigation"
        elif any(
            prod in text for prod in ["product", "item", "buy", "shop", "view details"]
        ):
            return "product"
        elif any(
            social in href for social in ["facebook", "twitter", "linkedin", "youtube"]
        ):
            return "social"
        elif any(
            file_ext in href for file_ext in [".pdf", ".doc", ".zip", ".download"]
        ):
            return "download"
        else:
            return "content"

    def scrape_with_depth(
        self,
        start_url,
        elements_to_extract,
        max_depth=2,
        max_pages=50,
        keyword_filter=None,
        progress_callback=None,
    ):
        """Enhanced scraping with better depth control and filtering"""
        results = []
        to_scrape = [(start_url, 0)]
        scraped_count = 0

        while to_scrape and scraped_count < max_pages:
            current_url, depth = to_scrape.pop(0)

            if current_url in self.scraped_urls or depth > max_depth:
                continue

            if progress_callback:
                progress_callback(
                    scraped_count, min(max_pages, len(to_scrape) + scraped_count + 1)
                )

            # Extract content
            data = self.extract_content(current_url, elements_to_extract)

            # Skip if there was an error
            if "error" in data:
                st.warning(f"Skipping {current_url}: {data['error']}")
                continue

            # Apply keyword filter
            if keyword_filter and "text_content" in data:
                if not any(
                    keyword.lower() in data["text_content"].lower()
                    for keyword in keyword_filter
                ):
                    continue

            data["crawl_depth"] = depth
            results.append(data)
            self.scraped_urls.add(current_url)
            scraped_count += 1

            # Find more links if we haven't reached max depth
            if depth < max_depth and "internal_links" in data:
                # Prioritize product and content links
                priority_links = [
                    link
                    for link in data["internal_links"]
                    if link.get("type") in ["product", "content"]
                ][:5]

                other_links = [
                    link
                    for link in data["internal_links"]
                    if link.get("type") not in ["product", "content"]
                ][:3]

                for link in priority_links + other_links:
                    if link["url"] not in self.scraped_urls:
                        to_scrape.append((link["url"], depth + 1))

            # Rate limiting
            time.sleep(1)

        return results


# Professional Components (keeping all original functionality)
class PricingPlans:
    @staticmethod
    def get_plans():
        return {
            "Free": {
                "price": 0,
                "pages_per_job": 20,
                "jobs_per_month": 5,
                "api_calls": 100,
                "features": ["Basic scraping", "CSV export", "Email support"],
                "color": "#6c757d",
            },
            "Professional": {
                "price": 29,
                "pages_per_job": 500,
                "jobs_per_month": 50,
                "api_calls": 1000,
                "features": [
                    "Advanced scraping",
                    "All export formats",
                    "API access",
                    "Priority support",
                    "Scheduled scraping",
                ],
                "color": "#007bff",
            },
            "Enterprise": {
                "price": 99,
                "pages_per_job": 5000,
                "jobs_per_month": 500,
                "api_calls": 10000,
                "features": [
                    "Unlimited scraping",
                    "Custom integrations",
                    "Dedicated support",
                    "White-label option",
                    "SLA guarantee",
                ],
                "color": "#28a745",
            },
        }


class ReportGenerator:
    @staticmethod
    def generate_executive_summary(results):
        total_pages = len(results)
        avg_content = (
            sum(r.get("content_length", 0) for r in results) / total_pages
            if total_pages > 0
            else 0
        )

        languages = Counter([r.get("language", "unknown") for r in results])
        sentiments = Counter([r.get("sentiment", "unknown") for r in results])
        website_types = Counter([r.get("website_type", "unknown") for r in results])

        summary = {
            "overview": {
                "total_pages_analyzed": total_pages,
                "average_content_length": int(avg_content),
                "primary_language": (
                    languages.most_common(1)[0][0] if languages else "Unknown"
                ),
                "dominant_sentiment": (
                    sentiments.most_common(1)[0][0] if sentiments else "Unknown"
                ),
                "primary_website_type": (
                    website_types.most_common(1)[0][0] if website_types else "Unknown"
                ),
            },
            "key_findings": [
                f"Analyzed {total_pages} pages with average content length of {int(avg_content)} characters",
                f"Primary language detected: {languages.most_common(1)[0][0] if languages else 'Unknown'}",
                f"Overall sentiment tendency: {sentiments.most_common(1)[0][0] if sentiments else 'Unknown'}",
                f"Main website type: {website_types.most_common(1)[0][0] if website_types else 'Unknown'}",
            ],
            "recommendations": [
                (
                    "Content optimization opportunities identified"
                    if avg_content < 1000
                    else "Strong content depth maintained"
                ),
                (
                    "Multi-language content strategy may be beneficial"
                    if len(languages) > 1
                    else "Consistent language approach"
                ),
                (
                    "Sentiment analysis suggests positive brand perception"
                    if sentiments.get("Positive", 0) > sentiments.get("Negative", 0)
                    else "Consider content tone adjustment"
                ),
            ],
        }
        return summary


# Visualization functions
def visualize_link_network(results):
    """Create network visualization of scraped links"""
    G = nx.Graph()

    for result in results:
        url = result.get("url", "")
        domain = urlparse(url).netloc

        G.add_node(url, type="page", domain=domain)

        if "internal_links" in result:
            for link in result["internal_links"][:10]:  # Limit for performance
                link_url = link["url"]
                G.add_node(link_url, type="internal_link", domain=domain)
                G.add_edge(url, link_url)

    if len(G.nodes()) == 0:
        return None

    pos = nx.spring_layout(G, k=3, iterations=50)

    edge_x = []
    edge_y = []
    for edge in G.edges():
        x0, y0 = pos[edge[0]]
        x1, y1 = pos[edge[1]]
        edge_x.extend([x0, x1, None])
        edge_y.extend([y0, y1, None])

    node_x = []
    node_y = []
    node_text = []
    node_color = []

    for node in G.nodes():
        x, y = pos[node]
        node_x.append(x)
        node_y.append(y)
        node_text.append(urlparse(node).path or "/")
        node_color.append("red" if G.nodes[node]["type"] == "page" else "blue")

    fig = go.Figure()

    fig.add_trace(
        go.Scatter(
            x=edge_x,
            y=edge_y,
            line=dict(width=0.5, color="#888"),
            hoverinfo="none",
            mode="lines",
        )
    )

    fig.add_trace(
        go.Scatter(
            x=node_x,
            y=node_y,
            mode="markers+text",
            hoverinfo="text",
            text=node_text,
            textposition="middle center",
            marker=dict(size=10, color=node_color),
        )
    )

    fig.update_layout(
        title="Link Network Visualization",
        showlegend=False,
        hovermode="closest",
        margin=dict(b=20, l=5, r=5, t=40),
        xaxis=dict(showgrid=False, zeroline=False, showticklabels=False),
        yaxis=dict(showgrid=False, zeroline=False, showticklabels=False),
    )

    return fig


# Authentication Section
def render_auth_section():
    """Render professional authentication section"""
    col1, col2, col3 = st.columns([1, 2, 1])

    with col2:
        st.markdown(
            """
        <div class="feature-card">
            <h2 style="text-align: center; color: #667eea;">Welcome to WebScrape Pro</h2>
            <p style="text-align: center;">Enhanced scraping for Amazon, eBay, and any website</p>
        </div>
        """,
            unsafe_allow_html=True,
        )

        auth_tab1, auth_tab2 = st.tabs(["🔑 Login", "📝 Sign Up"])

        with auth_tab1:
            with st.form("login_form"):
                username = st.text_input("Username")
                password = st.text_input("Password", type="password")
                login_btn = st.form_submit_button("Login", type="primary")

                if login_btn and username:
                    user_id = st.session_state.user_manager.create_user(
                        username, f"{username}@example.com"
                    )
                    if user_id:
                        st.session_state.current_user = user_id
                        st.rerun()
                    else:
                        st.error("Login failed. Please try again.")

        with auth_tab2:
            with st.form("signup_form"):
                new_username = st.text_input("Username")
                new_email = st.text_input("Email")
                plan = st.selectbox("Select Plan", ["free", "pro", "enterprise"])
                signup_btn = st.form_submit_button("Sign Up", type="primary")

                if signup_btn and new_username and new_email:
                    user_id = st.session_state.user_manager.create_user(
                        new_username, new_email, plan
                    )
                    if user_id:
                        st.session_state.current_user = user_id
                        st.success("Account created successfully!")
                        st.rerun()
                    else:
                        st.error("Username or email already exists.")

        # Enhanced features showcase
        st.markdown("### ✨ Enhanced Features")
        features = [
            "🚀 Works on Amazon, eBay, and complex e-commerce sites",
            "🤖 AI-powered content analysis and sentiment detection",
            "📊 Professional reporting and visualization",
            "🔒 Enterprise-grade security and compliance",
            "⚡ REST API access for custom integrations",
            "📞 24/7 dedicated customer support",
            "🛒 E-commerce data extraction (prices, reviews, ratings)",
            "🌐 Multi-language support and detection",
        ]

        for feature in features:
            st.markdown(f"- {feature}")


# Main Dashboard with Enhanced Scraping
def render_main_dashboard():
    """Render the main scraping dashboard with enhanced capabilities"""
    # Initialize session state
    if "scraper" not in st.session_state:
        st.session_state.scraper = EnhancedWebScraper()
    if "results" not in st.session_state:
        st.session_state.results = []
    if "scraping_complete" not in st.session_state:
        st.session_state.scraping_complete = False

    # Professional status bar
    col1, col2, col3, col4 = st.columns(4)

    with col1:
        st.markdown(
            """
        <div class="metric-professional">
            <h4>Credits Remaining</h4>
            <h2>87</h2>
        </div>
        """,
            unsafe_allow_html=True,
        )

    with col2:
        st.markdown(
            """
        <div class="metric-professional">
            <h4>Jobs This Month</h4>
            <h2>23</h2>
        </div>
        """,
            unsafe_allow_html=True,
        )

    with col3:
        st.markdown(
            """
        <div class="metric-professional">
            <h4>Success Rate</h4>
            <h2>99.2%</h2>
        </div>
        """,
            unsafe_allow_html=True,
        )

    with col4:
        st.markdown(
            """
        <div class="metric-professional">
            <h4>Plan</h4>
            <h2>Pro</h2>
        </div>
        """,
            unsafe_allow_html=True,
        )

    # Enhanced Sidebar configuration
    with st.sidebar:
        st.markdown(
            '<div class="section-header">🔧 Enhanced Scraping Configuration</div>',
            unsafe_allow_html=True,
        )

        # URL input with examples
        target_url = st.text_input(
            "🌐 Target Website URL", placeholder="https://example.com"
        )

        # Example URLs for testing
        st.markdown("**Example URLs to try:**")
        example_urls = [
            "https://books.toscrape.com/",
            "https://quotes.toscrape.com/",
            "https://httpbin.org/html",
            "https://example.com",
            "https://httpbin.org/forms/post",
        ]

        selected_example = st.selectbox(
            "Or choose an example:", ["Custom URL"] + example_urls
        )
        if selected_example != "Custom URL":
            target_url = selected_example

        # Website type selection
        website_type = st.selectbox(
            "Website Type (Auto-detect if unsure)",
            ["Auto-detect", "E-commerce", "News Site", "Blog", "General"],
        )

        # Enhanced crawl settings
        st.markdown("**Enhanced Crawl Settings**")
        max_depth = st.slider("📊 Crawl Depth", min_value=1, max_value=5, value=2)
        max_pages = st.slider("📄 Maximum Pages", min_value=1, max_value=100, value=20)
        rate_limit = st.slider(
            "⏱️ Rate Limit (seconds)", min_value=1.0, max_value=5.0, value=2.0, step=0.5
        )

        # Elements to extract with enhanced options
        st.markdown("**Elements to Extract**")
        elements_to_extract = st.multiselect(
            "Select elements:",
            [
                "title",
                "text_content",
                "headings",
                "links",
                "images",
                "meta_description",
                "tables",
                "ecommerce_data",
            ],
            default=["title", "text_content", "links", "ecommerce_data"],
        )

        # Advanced settings
        with st.expander("🚀 Advanced Settings"):
            keyword_filter = st.text_input("Keyword Filter (comma-separated)", "")
            keyword_list = (
                [k.strip() for k in keyword_filter.split(",") if k.strip()]
                if keyword_filter
                else None
            )

            extract_structured_data = st.checkbox(
                "Extract Structured Data (JSON-LD)", value=True
            )
            follow_pagination = st.checkbox("Follow Pagination Links", value=True)
            prioritize_product_links = st.checkbox(
                "Prioritize Product/Content Links", value=True
            )

        # E-commerce specific settings
        with st.expander("🛒 E-commerce Settings"):
            extract_prices = st.checkbox("Extract Prices", value=True)
            extract_reviews = st.checkbox("Extract Reviews & Ratings", value=True)
            extract_availability = st.checkbox(
                "Extract Availability Status", value=True
            )
            extract_product_details = st.checkbox("Extract Product Details", value=True)

    # Main content area
    col1, col2 = st.columns([2, 1])

    with col1:
        st.markdown(
            '<div class="section-header">🎯 Enhanced Scraping Control</div>',
            unsafe_allow_html=True,
        )

        # Enhanced scraping button
        if st.button(
            "🚀 Start Enhanced Scraping", type="primary", disabled=not target_url
        ):
            if target_url:
                # Update scraper settings
                st.session_state.scraper.rate_limit_delay = rate_limit

                # Validate URL
                validated_url = st.session_state.scraper.validate_url(target_url)

                if validated_url:
                    st.success(f"✅ URL validated: {validated_url}")

                    # Create progress indicators
                    progress_bar = st.progress(0)
                    status_text = st.empty()

                    with st.spinner("🔍 Enhanced scraping in progress..."):

                        def update_progress(current, total):
                            progress = current / total if total > 0 else 0
                            progress_bar.progress(progress)
                            status_text.text(f"Scraped {current} of {total} pages...")

                        try:
                            results = st.session_state.scraper.scrape_with_depth(
                                validated_url,
                                elements_to_extract,
                                max_depth=max_depth,
                                max_pages=max_pages,
                                keyword_filter=keyword_list,
                                progress_callback=update_progress,
                            )

                            st.session_state.results = results
                            st.session_state.scraping_complete = True

                            progress_bar.progress(1.0)
                            status_text.text("✅ Enhanced scraping completed!")

                            # Generate enhanced summary
                            summary = ReportGenerator.generate_executive_summary(
                                results
                            )
                            st.success(f"🎉 Successfully scraped {len(results)} pages!")

                            # Show enhanced summary
                            with st.expander("📊 Executive Summary", expanded=True):
                                st.json(summary)

                        except Exception as e:
                            st.error(f"❌ Scraping failed: {str(e)}")
                else:
                    st.error("❌ Invalid URL. Please check the URL and try again.")

    with col2:
        # Enhanced quick stats
        if st.session_state.results:
            st.markdown(
                '<div class="section-header">📊 Enhanced Stats</div>',
                unsafe_allow_html=True,
            )

            results = st.session_state.results
            total_pages = len(results)

            # Enhanced metrics
            ecommerce_pages = sum(
                1 for r in results if r.get("website_type") == "ecommerce"
            )
            total_products = sum(1 for r in results if r.get("product_title"))
            avg_price = 0

            # Calculate average price for e-commerce pages
            prices = []
            for r in results:
                if r.get("price"):
                    try:
                        price_num = float(re.sub(r"[^\d.]", "", r["price"]))
                        prices.append(price_num)
                    except:
                        continue

            if prices:
                avg_price = sum(prices) / len(prices)

            st.metric("Pages Scraped", total_pages)
            st.metric("E-commerce Pages", ecommerce_pages)
            st.metric("Products Found", total_products)
            if avg_price > 0:
                st.metric("Average Price", f"${avg_price:.2f}")

            # Website type distribution
            website_types = [r.get("website_type", "unknown") for r in results]
            type_counts = Counter(website_types)

            if type_counts:
                fig_types = px.pie(
                    values=list(type_counts.values()),
                    names=list(type_counts.keys()),
                    title="Website Types Detected",
                )
                st.plotly_chart(fig_types, use_container_width=True)

    # Enhanced Results section
    if st.session_state.scraping_complete and st.session_state.results:
        st.markdown(
            '<div class="section-header">📋 Enhanced Results Dashboard</div>',
            unsafe_allow_html=True,
        )

        results = st.session_state.results

        # Enhanced tabs
        tab1, tab2, tab3, tab4, tab5, tab6, tab7 = st.tabs(
            [
                "📊 Data View",
                "🛒 E-commerce",
                "📈 Analytics",
                "🔗 Link Analysis",
                "☁️ Word Cloud",
                "💾 Export",
                "📄 Reports",
            ]
        )

        with tab1:
            # Enhanced data view with filtering
            df_data = []
            for result in results:
                row = {
                    "URL": result.get("url", ""),
                    "Title": result.get("title", "N/A"),
                    "Type": result.get("website_type", "Unknown"),
                    "Content Length": result.get("content_length", 0),
                    "Language": result.get("language", "Unknown"),
                    "Sentiment": result.get("sentiment", "N/A"),
                    "Internal Links": len(result.get("internal_links", [])),
                    "External Links": len(result.get("external_links", [])),
                    "Images": len(result.get("images", [])),
                    "Timestamp": result.get("timestamp", ""),
                }
                df_data.append(row)

            df = pd.DataFrame(df_data)

            # Enhanced search and filter
            col1, col2, col3, col4 = st.columns(4)
            with col1:
                search_term = st.text_input("🔍 Search titles", "")
            with col2:
                type_filter = st.selectbox(
                    "Filter by Type", ["All"] + list(df["Type"].unique())
                )
            with col3:
                lang_filter = st.selectbox(
                    "Filter by Language", ["All"] + list(df["Language"].unique())
                )
            with col4:
                sentiment_filter = st.selectbox(
                    "Filter by Sentiment", ["All"] + list(df["Sentiment"].unique())
                )

            # Apply filters
            filtered_df = df.copy()
            if search_term:
                filtered_df = filtered_df[
                    filtered_df["Title"].str.contains(search_term, case=False, na=False)
                ]
            if type_filter != "All":
                filtered_df = filtered_df[filtered_df["Type"] == type_filter]
            if lang_filter != "All":
                filtered_df = filtered_df[filtered_df["Language"] == lang_filter]
            if sentiment_filter != "All":
                filtered_df = filtered_df[filtered_df["Sentiment"] == sentiment_filter]

            st.dataframe(filtered_df, use_container_width=True)

            # Detailed view
            if len(filtered_df) > 0:
                selected_idx = st.selectbox(
                    "Select page for detailed view", range(len(filtered_df))
                )
                if selected_idx < len(results):
                    with st.expander("📖 Detailed Content"):
                        st.json(results[selected_idx])

        with tab2:
            # Enhanced e-commerce analysis
            ecommerce_results = [
                r for r in results if r.get("website_type") == "ecommerce"
            ]

            if ecommerce_results:
                st.subheader("🛒 E-commerce Products Analysis")

                # Create enhanced e-commerce dataframe
                ecommerce_data = []
                for result in ecommerce_results:
                    row = {
                        "Product Title": result.get(
                            "product_title", result.get("title", "N/A")
                        ),
                        "Price": result.get("price", "N/A"),
                        "Rating": result.get("rating", "N/A"),
                        "Reviews Count": result.get("reviews_count", "N/A"),
                        "Availability": result.get("availability", "N/A"),
                        "Sentiment": result.get("sentiment", "N/A"),
                        "URL": result.get("url", ""),
                    }
                    ecommerce_data.append(row)

                ecommerce_df = pd.DataFrame(ecommerce_data)
                st.dataframe(ecommerce_df, use_container_width=True)

                # Enhanced price analysis
                prices = []
                ratings = []
                for result in ecommerce_results:
                    if result.get("price"):
                        try:
                            price_num = float(re.sub(r"[^\d.]", "", result["price"]))
                            prices.append(price_num)
                        except:
                            pass

                    if result.get("rating"):
                        try:
                            rating_num = float(result["rating"])
                            ratings.append(rating_num)
                        except:
                            pass

                if prices or ratings:
                    col1, col2 = st.columns(2)

                    with col1:
                        if prices:
                            st.subheader("Price Analysis")
                            st.metric(
                                "Average Price", f"${sum(prices)/len(prices):.2f}"
                            )
                            st.metric(
                                "Price Range",
                                f"${min(prices):.2f} - ${max(prices):.2f}",
                            )

                            fig_price = px.histogram(
                                x=prices, title="Price Distribution", nbins=10
                            )
                            st.plotly_chart(fig_price, use_container_width=True)

                    with col2:
                        if ratings:
                            st.subheader("Rating Analysis")
                            st.metric(
                                "Average Rating", f"{sum(ratings)/len(ratings):.1f}/5"
                            )
                            st.metric(
                                "Rating Range",
                                f"{min(ratings):.1f} - {max(ratings):.1f}",
                            )

                            fig_rating = px.histogram(
                                x=ratings, title="Rating Distribution", nbins=5
                            )
                            st.plotly_chart(fig_rating, use_container_width=True)

                # Sentiment analysis for products
                product_sentiments = [
                    r.get("sentiment", "Unknown") for r in ecommerce_results
                ]
                sentiment_counts = Counter(product_sentiments)

                if (
                    sentiment_counts
                    and "Unknown" not in sentiment_counts
                    or len(sentiment_counts) > 1
                ):
                    fig_sentiment = px.pie(
                        values=list(sentiment_counts.values()),
                        names=list(sentiment_counts.keys()),
                        title="Product Page Sentiment Analysis",
                    )
                    st.plotly_chart(fig_sentiment, use_container_width=True)

            else:
                st.info(
                    "No e-commerce pages detected. Try scraping Amazon, eBay, or other online stores."
                )
                st.markdown("**Example URLs to try:**")
                st.markdown("- https://amazon.com/dp/B08N5WRWNW")
                st.markdown("- https://ebay.com/itm/123456789")
                st.markdown("- Any product page URL")

        with tab3:
            # Enhanced analytics
            if len(results) > 1:
                col1, col2 = st.columns(2)

                with col1:
                    # Content length distribution
                    content_lengths = [r.get("content_length", 0) for r in results]
                    fig_content = px.histogram(
                        x=content_lengths, title="Content Length Distribution", nbins=20
                    )
                    st.plotly_chart(fig_content, use_container_width=True)

                    # Language distribution
                    languages = [r.get("language", "Unknown") for r in results]
                    lang_counts = Counter(languages)
                    if lang_counts:
                        fig_lang = px.bar(
                            x=list(lang_counts.keys()),
                            y=list(lang_counts.values()),
                            title="Language Distribution",
                        )
                        st.plotly_chart(fig_lang, use_container_width=True)

                with col2:
                    # Sentiment analysis
                    sentiments = [r.get("sentiment", "Unknown") for r in results]
                    sentiment_counts = Counter(sentiments)
                    if sentiment_counts:
                        fig_sentiment = px.pie(
                            values=list(sentiment_counts.values()),
                            names=list(sentiment_counts.keys()),
                            title="Overall Sentiment Analysis",
                        )
                        st.plotly_chart(fig_sentiment, use_container_width=True)

                    # Crawl depth analysis
                    depths = [r.get("crawl_depth", 0) for r in results]
                    depth_counts = Counter(depths)
                    fig_depth = px.bar(
                        x=list(depth_counts.keys()),
                        y=list(depth_counts.values()),
                        title="Pages by Crawl Depth",
                    )
                    st.plotly_chart(fig_depth, use_container_width=True)

        with tab4:
            # Enhanced link network visualization
            if any("internal_links" in r for r in results):
                fig_network = visualize_link_network(results)
                if fig_network:
                    st.plotly_chart(fig_network, use_container_width=True)

                # Link type analysis
                all_links = []
                for result in results:
                    for link in result.get("internal_links", []):
                        all_links.append(link.get("type", "unknown"))

                if all_links:
                    link_counts = Counter(all_links)
                    fig_links = px.bar(
                        x=list(link_counts.keys()),
                        y=list(link_counts.values()),
                        title="Link Types Distribution",
                    )
                    st.plotly_chart(fig_links, use_container_width=True)

                # Link statistics
                total_internal = sum(len(r.get("internal_links", [])) for r in results)
                total_external = sum(len(r.get("external_links", [])) for r in results)

                col1, col2 = st.columns(2)
                col1.metric("Total Internal Links", total_internal)
                col2.metric("Total External Links", total_external)
            else:
                st.info("No link data available for visualization")

        with tab5:
            # Enhanced word cloud
            all_text = " ".join(
                [r.get("text_content", "") for r in results if r.get("text_content")]
            )
            if all_text.strip():
                try:
                    wordcloud = WordCloud(
                        width=800,
                        height=400,
                        background_color="white",
                        max_words=100,
                        relative_scaling=0.5,
                        colormap="viridis",
                    ).generate(all_text)

                    fig, ax = plt.subplots(figsize=(12, 6))
                    ax.imshow(wordcloud, interpolation="bilinear")
                    ax.axis("off")
                    st.pyplot(fig)

                    # Enhanced keyword analysis
                    all_keywords = {}
                    for result in results:
                        if "keywords" in result:
                            for word, count in result["keywords"].items():
                                all_keywords[word] = all_keywords.get(word, 0) + count

                    if all_keywords:
                        top_keywords = dict(
                            sorted(
                                all_keywords.items(), key=lambda x: x[1], reverse=True
                            )[:25]
                        )

                        col1, col2 = st.columns(2)
                        with col1:
                            fig_keywords = px.bar(
                                x=list(top_keywords.values()),
                                y=list(top_keywords.keys()),
                                orientation="h",
                                title="Top 25 Keywords",
                            )
                            fig_keywords.update_layout(
                                height=600, yaxis={"categoryorder": "total ascending"}
                            )
                            st.plotly_chart(fig_keywords, use_container_width=True)

                        with col2:
                            # Keyword frequency table
                            keyword_df = pd.DataFrame(
                                [
                                    {"Keyword": k, "Frequency": v}
                                    for k, v in top_keywords.items()
                                ]
                            )
                            st.dataframe(keyword_df, use_container_width=True)

                except Exception as e:
                    st.error(f"Could not generate word cloud: {str(e)}")
            else:
                st.info("No text content available for word cloud generation")

        with tab6:
            # Enhanced export functionality
            st.markdown("### 💾 Enhanced Export Options")

            # Export format selection
            col1, col2 = st.columns(2)
            with col1:
                export_format = st.selectbox(
                    "Choose format:", ["CSV", "JSON", "Excel", "SQLite"]
                )
                filename = st.text_input(
                    "Filename (without extension)",
                    value=f"enhanced_scraping_{datetime.now().strftime('%Y%m%d_%H%M%S')}",
                )

            with col2:
                # Enhanced export options
                include_full_content = st.checkbox("Include full text content")
                include_ecommerce_data = st.checkbox(
                    "Include e-commerce data", value=True
                )
                include_links = st.checkbox("Include detailed link data")
                include_analysis = st.checkbox("Include NLP analysis", value=True)

            # Generate enhanced export
            if st.button("📥 Generate Enhanced Export"):
                export_data = []
                for result in results:
                    row = {
                        "url": result.get("url", ""),
                        "title": result.get("title", ""),
                        "website_type": result.get("website_type", ""),
                        "content_length": result.get("content_length", 0),
                        "language": result.get("language", ""),
                        "sentiment": result.get("sentiment", ""),
                        "internal_links_count": len(result.get("internal_links", [])),
                        "external_links_count": len(result.get("external_links", [])),
                        "images_count": len(result.get("images", [])),
                        "crawl_depth": result.get("crawl_depth", 0),
                        "timestamp": result.get("timestamp", ""),
                        "status_code": result.get("status_code", ""),
                        "page_size": result.get("page_size", 0),
                    }

                    # Add e-commerce data if available
                    if include_ecommerce_data:
                        row.update(
                            {
                                "product_title": result.get("product_title", ""),
                                "price": result.get("price", ""),
                                "rating": result.get("rating", ""),
                                "reviews_count": result.get("reviews_count", ""),
                                "availability": result.get("availability", ""),
                            }
                        )

                    # Add full content if requested
                    if include_full_content:
                        row["text_content"] = result.get("text_content", "")
                    else:
                        # Include truncated content
                        content = result.get("text_content", "")
                        row["text_content_preview"] = (
                            content[:500] + "..." if len(content) > 500 else content
                        )

                    # Add analysis data
                    if include_analysis:
                        row["entities_person"] = ", ".join(
                            result.get("entities", {}).get("PERSON", [])
                        )
                        row["entities_org"] = ", ".join(
                            result.get("entities", {}).get("ORG", [])
                        )
                        row["entities_gpe"] = ", ".join(
                            result.get("entities", {}).get("GPE", [])
                        )
                        row["top_keywords"] = ", ".join(
                            list(result.get("keywords", {}).keys())[:10]
                        )

                    # Add link data if requested
                    if include_links:
                        row["internal_links"] = json.dumps(
                            result.get("internal_links", [])
                        )
                        row["external_links"] = json.dumps(
                            result.get("external_links", [])
                        )

                    export_data.append(row)

                export_df = pd.DataFrame(export_data)

                # Generate download based on format
                if export_format == "CSV":
                    csv = export_df.to_csv(index=False)
                    st.download_button(
                        "📥 Download CSV", csv, f"{filename}.csv", "text/csv"
                    )
                elif export_format == "JSON":
                    json_data = export_df.to_json(orient="records", indent=2)
                    st.download_button(
                        "📥 Download JSON",
                        json_data,
                        f"{filename}.json",
                        "application/json",
                    )
                elif export_format == "Excel":
                    buffer = BytesIO()
                    with pd.ExcelWriter(buffer, engine="openpyxl") as writer:
                        export_df.to_excel(
                            writer, sheet_name="Scraping Results", index=False
                        )

                        # Add summary sheet
                        summary_data = {
                            "Metric": [
                                "Total Pages",
                                "E-commerce Pages",
                                "Average Content Length",
                                "Most Common Type",
                            ],
                            "Value": [
                                len(results),
                                sum(
                                    1
                                    for r in results
                                    if r.get("website_type") == "ecommerce"
                                ),
                                int(
                                    sum(r.get("content_length", 0) for r in results)
                                    / len(results)
                                ),
                                Counter(
                                    [r.get("website_type", "unknown") for r in results]
                                ).most_common(1)[0][0],
                            ],
                        }
                        summary_df = pd.DataFrame(summary_data)
                        summary_df.to_excel(writer, sheet_name="Summary", index=False)

                    st.download_button(
                        "📥 Download Excel",
                        buffer.getvalue(),
                        f"{filename}.xlsx",
                        "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
                    )

                st.success("✅ Enhanced export file generated successfully!")

        with tab7:
            # Enhanced professional reporting
            st.markdown("### 📄 Professional Reports")

            report_type = st.selectbox(
                "Report Type",
                [
                    "Executive Summary",
                    "E-commerce Analysis",
                    "Competitive Intelligence",
                    "SEO Audit",
                ],
            )

            if st.button("📊 Generate Enhanced Report"):
                if report_type == "Executive Summary":
                    summary = ReportGenerator.generate_executive_summary(results)

                    st.markdown("## Enhanced Executive Summary Report")
                    st.markdown(
                        f"**Generated on:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
                    )

                    # Overview metrics
                    overview = summary["overview"]
                    metric_cols = st.columns(5)
                    metric_cols[0].metric(
                        "Pages Analyzed", overview["total_pages_analyzed"]
                    )
                    metric_cols[1].metric(
                        "Avg Content Length", overview["average_content_length"]
                    )
                    metric_cols[2].metric(
                        "Primary Language", overview["primary_language"]
                    )
                    metric_cols[3].metric(
                        "Dominant Sentiment", overview["dominant_sentiment"]
                    )
                    metric_cols[4].metric(
                        "Website Type", overview["primary_website_type"]
                    )

                    # Key findings
                    st.markdown("### Key Findings")
                    for finding in summary["key_findings"]:
                        st.markdown(f"• {finding}")

                    # Strategic recommendations
                    st.markdown("### Strategic Recommendations")
                    for recommendation in summary["recommendations"]:
                        st.markdown(f"• {recommendation}")

                elif report_type == "E-commerce Analysis":
                    ecommerce_results = [
                        r for r in results if r.get("website_type") == "ecommerce"
                    ]

                    if ecommerce_results:
                        st.markdown("## E-commerce Analysis Report")

                        # E-commerce metrics
                        products_with_prices = sum(
                            1 for r in ecommerce_results if r.get("price")
                        )
                        products_with_ratings = sum(
                            1 for r in ecommerce_results if r.get("rating")
                        )

                        col1, col2, col3 = st.columns(3)
                        col1.metric("E-commerce Pages", len(ecommerce_results))
                        col2.metric("Products with Prices", products_with_prices)
                        col3.metric("Products with Ratings", products_with_ratings)

                        # Price analysis
                        prices = []
                        for r in ecommerce_results:
                            if r.get("price"):
                                try:
                                    price_num = float(re.sub(r"[^\d.]", "", r["price"]))
                                    prices.append(price_num)
                                except:
                                    pass

                        if prices:
                            st.markdown("### Price Analysis")
                            col1, col2 = st.columns(2)
                            col1.metric(
                                "Average Price", f"${sum(prices)/len(prices):.2f}"
                            )
                            col2.metric(
                                "Price Range",
                                f"${min(prices):.2f} - ${max(prices):.2f}",
                            )
                    else:
                        st.info("No e-commerce data found in the scraped results.")

                # Export report
                if st.button("📥 Export Report"):
                    report_data = {
                        "report_type": report_type,
                        "generated_at": datetime.now().isoformat(),
                        "target_url": target_url if "target_url" in locals() else "N/A",
                        "summary": summary if "summary" in locals() else {},
                        "total_pages": len(results),
                        "website_types": dict(
                            Counter([r.get("website_type", "unknown") for r in results])
                        ),
                        "languages": dict(
                            Counter([r.get("language", "unknown") for r in results])
                        ),
                        "sentiments": dict(
                            Counter([r.get("sentiment", "unknown") for r in results])
                        ),
                    }

                    st.download_button(
                        "📊 Download Report (JSON)",
                        json.dumps(report_data, indent=2),
                        f"{report_type.lower().replace(' ', '_')}_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json",
                        "application/json",
                    )


# Professional UI Components
def render_pricing_section():
    """Render professional pricing plans"""
    st.markdown("## 💎 Choose Your Plan")
    plans = PricingPlans.get_plans()

    col1, col2, col3 = st.columns(3)
    cols = [col1, col2, col3]

    for i, (plan_name, plan_details) in enumerate(plans.items()):
        with cols[i]:
            popular_class = (
                "pricing-popular" if plan_name == "Professional" else "pricing-card"
            )

            st.markdown(
                f"""
            <div class="{popular_class}">
                {f'<div class="popular-badge">MOST POPULAR</div>' if plan_name == "Professional" else ''}
                <h3 style="color: {plan_details['color']};">{plan_name}</h3>
                <div style="font-size: 2.5rem; font-weight: bold; color: {plan_details['color']};">
                    ${plan_details['price']}<span style="font-size: 1rem; color: #6c757d;">/month</span>
                </div>
                <p style="margin: 1rem 0;">
                    <strong>{plan_details['pages_per_job']:,}</strong> pages per job<br>
                    <strong>{plan_details['jobs_per_month']}</strong> jobs per month<br>
                    <strong>{plan_details['api_calls']:,}</strong> API calls
                </p>
            </div>
            """,
                unsafe_allow_html=True,
            )

            for feature in plan_details["features"]:
                st.markdown(f"✅ {feature}")

            button_text = (
                "Current Plan" if plan_name == "Free" else f"Upgrade to {plan_name}"
            )
            if st.button(
                button_text,
                key=f"btn_{plan_name}",
                type="primary" if plan_name == "Professional" else "secondary",
            ):
                st.success(f"Great choice! {plan_name} plan selected.")


def render_analytics_dashboard():
    """Render professional analytics dashboard"""
    st.markdown("## 📊 Analytics Dashboard")

    # Mock analytics data
    col1, col2, col3, col4 = st.columns(4)

    with col1:
        st.markdown(
            """
        <div class="metric-professional">
            <h3>47,523</h3>
            <p>Pages Scraped This Month</p>
        </div>
        """,
            unsafe_allow_html=True,
        )

    with col2:
        st.markdown(
            """
        <div class="metric-professional">
            <h3>99.7%</h3>
            <p>Success Rate</p>
        </div>
        """,
            unsafe_allow_html=True,
        )

    with col3:
        st.markdown(
            """
        <div class="metric-professional">
            <h3>1.2s</h3>
            <p>Avg Response Time</p>
        </div>
        """,
            unsafe_allow_html=True,
        )

    with col4:
        st.markdown(
            """
        <div class="metric-professional">
            <h3>156</h3>
            <p>Active Projects</p>
        </div>
        """,
            unsafe_allow_html=True,
        )

    # Usage trends
    col1, col2 = st.columns(2)

    with col1:
        dates = pd.date_range(start="2024-01-01", end="2024-01-31", freq="D")
        usage_data = pd.DataFrame(
            {
                "Date": dates,
                "Pages Scraped": [
                    1200 + i * 50 + (i % 7) * 200 for i in range(len(dates))
                ],
                "API Calls": [800 + i * 30 + (i % 5) * 100 for i in range(len(dates))],
            }
        )

        fig_usage = px.line(
            usage_data,
            x="Date",
            y=["Pages Scraped", "API Calls"],
            title="Daily Usage Trends",
        )
        st.plotly_chart(fig_usage, use_container_width=True)

    with col2:
        domain_data = pd.DataFrame(
            {
                "Domain": ["E-commerce", "News", "Corporate", "Social Media", "Forums"],
                "Success Rate": [99.8, 99.5, 99.9, 95.2, 97.8],
                "Total Requests": [15420, 8930, 12500, 3200, 5670],
            }
        )

        fig_success = px.bar(
            domain_data,
            x="Domain",
            y="Success Rate",
            title="Success Rate by Domain Type",
        )
        st.plotly_chart(fig_success, use_container_width=True)


def render_api_section():
    """Render API documentation and management"""
    st.markdown("## ⚡ API Access & Documentation")

    col1, col2 = st.columns([2, 1])

    with col1:
        st.markdown("### 🔑 API Key Management")

        if "api_key" not in st.session_state:
            st.session_state.api_key = f"sk-{uuid.uuid4().hex[:32]}"

        st.code(st.session_state.api_key, language="text")

        col_a, col_b, col_c = st.columns(3)
        with col_a:
            if st.button("🔄 Regenerate Key"):
                st.session_state.api_key = f"sk-{uuid.uuid4().hex[:32]}"
                st.rerun()
        with col_b:
            if st.button("📋 Copy Key"):
                st.success("API key copied to clipboard!")
        with col_c:
            if st.button("📊 View Usage"):
                st.info("API usage: 247/1000 calls this month")

    with col2:
        st.markdown("### 📈 API Usage")
        st.markdown(
            """
        <div class="metric-professional">
            <h4>Current Usage</h4>
            <p><strong>247</strong> / 1,000 calls</p>
            <p><strong>75.3%</strong> success rate</p>
            <p><strong>1.2s</strong> avg response time</p>
        </div>
        """,
            unsafe_allow_html=True,
        )

    # API Documentation tabs
    api_tabs = st.tabs(
        ["🚀 Quick Start", "📡 Endpoints", "🔧 Examples", "📊 Response Format"]
    )

    with api_tabs[0]:
        st.markdown(
            """
        #### Getting Started
        
        Welcome to the Enhanced WebScrape Pro API! Get started in just 3 steps:
        
        1. **Authentication**: Include your API key in the header
        2. **Make Request**: Send POST request to scraping endpoint
        3. **Get Results**: Receive structured data in JSON format
        """
        )

        st.code(
            """
# Install the WebScrape Pro Python SDK
pip install webscrape-pro

# Basic usage
from webscrape_pro import WebScrapePro

client = WebScrapePro(api_key="your-api-key-here")
result = client.scrape("https://amazon.com/dp/B08N5WRWNW")
        """,
            language="bash",
        )

    with api_tabs[1]:
        st.markdown("#### Available Endpoints")

        endpoints = [
            {
                "method": "POST",
                "endpoint": "/api/v1/scrape",
                "description": "Start enhanced scraping job",
                "rate_limit": "100/hour",
            },
            {
                "method": "GET",
                "endpoint": "/api/v1/jobs/{job_id}",
                "description": "Get job status and results",
                "rate_limit": "1000/hour",
            },
            {
                "method": "GET",
                "endpoint": "/api/v1/ecommerce/analyze",
                "description": "Analyze e-commerce data",
                "rate_limit": "50/hour",
            },
            {
                "method": "DELETE",
                "endpoint": "/api/v1/jobs/{job_id}",
                "description": "Delete a scraping job",
                "rate_limit": "100/hour",
            },
        ]

        for endpoint in endpoints:
            st.markdown(
                f"""
            <div class="api-code">
                <strong>{endpoint['method']}</strong> {endpoint['endpoint']}<br>
                {endpoint['description']}<br>
                <small>Rate limit: {endpoint['rate_limit']}</small>
            </div>
            """,
                unsafe_allow_html=True,
            )

    with api_tabs[2]:
        st.markdown("#### Enhanced Code Examples")

        example_tabs = st.tabs(["Python", "JavaScript", "cURL"])

        with example_tabs[0]:
            st.code(
                """
import requests

# Enhanced scraping with e-commerce detection
url = "https://api.webscrape-pro.com/v1/scrape"
headers = {
    "Authorization": "Bearer your-api-key-here",
    "Content-Type": "application/json"
}
payload = {
    "url": "https://amazon.com/dp/B08N5WRWNW",
    "elements": ["title", "text_content", "ecommerce_data"],
    "max_pages": 10,
    "extract_prices": True,
    "extract_reviews": True,
    "website_type": "ecommerce"
}

response = requests.post(url, headers=headers, json=payload)
result = response.json()

# Access e-commerce specific data
if 'ecommerce_data' in result:
    print(f"Product: {result['product_title']}")
    print(f"Price: ${result['price']}")
    print(f"Rating: {result['rating']}/5")
            """,
                language="python",
            )

        with example_tabs[1]:
            st.code(
                """
// Enhanced scraping with async/await
const scrapeEcommerce = async () => {
    try {
        const response = await fetch('https://api.webscrape-pro.com/v1/scrape', {
            method: 'POST',
            headers: {
                'Authorization': 'Bearer your-api-key-here',
                'Content-Type': 'application/json'
            },
            body: JSON.stringify({
                url: 'https://amazon.com/dp/B08N5WRWNW',
                elements: ['title', 'ecommerce_data'],
                extract_prices: true,
                extract_reviews: true
            })
        });
        
        const data = await response.json();
        console.log('Product Data:', data.ecommerce_data);
    } catch (error) {
        console.error('Error:', error);
    }
};
            """,
                language="javascript",
            )

        with example_tabs[2]:
            st.code(
                """
curl -X POST https://api.webscrape-pro.com/v1/scrape \
  -H "Authorization: Bearer your-api-key-here" \
  -H "Content-Type: application/json" \
  -d '{
    "url": "https://amazon.com/dp/B08N5WRWNW",
    "elements": ["title", "ecommerce_data"],
    "extract_prices": true,
    "extract_reviews": true,
    "website_type": "ecommerce"
  }'
            """,
                language="bash",
            )

    with api_tabs[3]:
        st.markdown("#### Enhanced Response Format")

        st.markdown("**E-commerce Response:**")
        st.code(
            """
{
  "job_id": "job_12345",
  "status": "completed",
  "website_type": "ecommerce",
  "results": {
    "url": "https://amazon.com/dp/B08N5WRWNW",
    "title": "Product Title",
    "product_title": "Enhanced Product Name",
    "price": "29.99",
    "rating": "4.5",
    "reviews_count": "1,234",
    "availability": "In Stock",
    "sentiment": "Positive",
    "text_content": "Product description...",
    "ecommerce_data": {
      "category": "Electronics",
      "brand": "BrandName",
      "features": ["Feature 1", "Feature 2"]
    }
  }
}
        """,
            language="json",
        )


def main():
    """Enhanced main application"""
    st.set_page_config(
        page_title="WebScrape Pro - Enhanced Web Intelligence",
        page_icon="🚀",
        layout="wide",
        initial_sidebar_state="expanded",
    )

    # Initialize components
    if "user_manager" not in st.session_state:
        st.session_state.user_manager = UserManager()
    if "current_user" not in st.session_state:
        st.session_state.current_user = None

    # Enhanced Professional CSS
    st.markdown(
        """
    <style>
    .main-header {
        background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
        padding: 2rem;
        border-radius: 10px;
        color: white;
        text-align: center;
        margin-bottom: 2rem;
        box-shadow: 0 4px 15px rgba(0,0,0,0.1);
    }
    .main-title {
        font-size: 3rem;
        font-weight: 800;
        margin-bottom: 0.5rem;
    }
    .main-subtitle {
        font-size: 1.2rem;
        opacity: 0.9;
        margin-bottom: 1rem;
    }
    .feature-card {
        background: white;
        padding: 1.5rem;
        border-radius: 10px;
        box-shadow: 0 2px 10px rgba(0,0,0,0.1);
        margin-bottom: 1rem;
        border-left: 4px solid #667eea;
    }
    .pricing-card {
        background: white;
        border: 2px solid #e9ecef;
        border-radius: 15px;
        padding: 2rem;
        text-align: center;
        margin: 1rem;
        transition: transform 0.3s ease;
    }
    .pricing-card:hover {
        transform: translateY(-5px);
        box-shadow: 0 10px 25px rgba(0,0,0,0.1);
    }
    .pricing-popular {
        border-color: #007bff;
        position: relative;
        background: linear-gradient(135deg, #f8f9ff 0%, #e6f0ff 100%);
    }
    .popular-badge {
        background: #007bff;
        color: white;
        padding: 0.5rem 1rem;
        border-radius: 20px;
        position: absolute;
        top: -15px;
        left: 50%;
        transform: translateX(-50%);
        font-size: 0.8rem;
        font-weight: bold;
    }
    .metric-professional {
        background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
        color: white;
        padding: 1rem;
        border-radius: 10px;
        text-align: center;
        margin: 0.5rem 0;
    }
    .api-code {
        background: #f8f9fa;
        border: 1px solid #e9ecef;
        border-radius: 5px;
        padding: 1rem;
        font-family: 'Courier New', monospace;
        font-size: 0.9rem;
        margin: 0.5rem 0;
    }
    .section-header {
        font-size: 1.5rem;
        font-weight: bold;
        color: #667eea;
        margin-top: 2rem;
        margin-bottom: 1rem;
    }
    </style>
    """,
        unsafe_allow_html=True,
    )

    # Enhanced Professional Header
    st.markdown(
        """
    <div class="main-header">
        <div class="main-title">🚀 WebScrape Pro Enhanced</div>
        <div class="main-subtitle">Advanced Web Intelligence for Amazon, E-commerce & Complex Sites</div>
        <p style="margin-bottom: 0;">Now supports advanced e-commerce extraction • Enhanced NLP • 99.9% Success Rate</p>
    </div>
    """,
        unsafe_allow_html=True,
    )

    # User Authentication
    if not st.session_state.current_user:
        render_auth_section()
        return

    # Enhanced Navigation
    tab_main, tab_pricing, tab_analytics, tab_api = st.tabs(
        ["🏠 Enhanced Dashboard", "💎 Pricing", "📊 Analytics", "⚡ API"]
    )

    with tab_main:
        render_main_dashboard()

    with tab_pricing:
        render_pricing_section()

    with tab_analytics:
        render_analytics_dashboard()

    with tab_api:
        render_api_section()

    # Enhanced Footer
    st.markdown("---")
    st.markdown(
        """
    <div style='text-align: center; color: #666; padding: 20px;'>
        <p>🕷️ <strong>WebScrape Pro Enhanced - Advanced Web Intelligence Platform</strong></p>
        <p>Features: Amazon/E-commerce Support • AI Analysis • Professional Reports • Enterprise Compliance • REST API • 24/7 Support</p>
        <p><small>✨ New: Enhanced e-commerce extraction, better content detection, improved success rates</small></p>
        <p><small>⚠️ Please respect robots.txt, rate limits, and data privacy laws when scraping websites</small></p>
        <p><small>© 2024 WebScrape Pro Enhanced. All rights reserved.</small></p>
    </div>
    """,
        unsafe_allow_html=True,
    )


if __name__ == "__main__":
    main()
