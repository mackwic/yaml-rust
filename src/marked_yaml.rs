use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::ops::Index;
use std::string;
use std::i64;
use std::mem;
use std::vec;
use parser::*;
use scanner::{TScalarStyle, ScanError, TokenType, Marker};

#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct Source {
    pub file: String,
    // TODO: make it a &str
    pub start: Marker,
    // pub end: Marker, TODO: maybe one day ?
}

/// A Marked YAML node is stored as this `Yaml` enumeration, which provides an easy way to
/// access your YAML document.
///
/// # Examples
///
/// ```
/// use yaml_rust::Yaml;
/// let foo = Yaml::from_str("-123"); // convert the string to the appropriate YAML type
/// assert_eq!(foo.as_i64().unwrap(), -123);
///
/// // iterate over an Array
/// let vec = Yaml::Array(vec![Yaml::Integer(1), Yaml::Integer(2)]);
/// for v in vec.as_vec().unwrap() {
///     assert!(v.as_i64().is_some());
/// }
/// ```
#[derive(Clone, PartialEq, Debug, Eq)]
pub enum MarkedYaml {
    /// Float types are stored as String and parsed on demand.
    /// Note that f64 does NOT implement Eq trait and can NOT be stored in BTreeMap.
    Real(string::String, Source),
    /// YAML int is stored as i64.
    Integer(i64, Source),
    /// YAML scalar.
    String(string::String, Source),
    /// YAML bool, e.g. `true` or `false`.
    Boolean(bool, Source),
    /// YAML array, can be accessed as a `Vec`.
    Array(self::Array, Source),
    /// YAML hash, can be accessed as a `BTreeMap`.
    ///
    /// If the order of keys is meaningful, enable the `preserve_order` feature to
    /// store hashes as a `LinkedHashMap` intead of `BTreeMap`. When using a
    /// `LinkedHashMap`, the itertion order will match the order of insertion into
    /// the map.
    ///
    /// ```toml
    /// yaml-rust = { version = "*", features = ["preserve_order"] }
    /// ```
    Hash(self::Hash, Source),
    /// Alias, not fully supported yet.
    Alias(usize, Source),
    /// YAML null, e.g. `null` or `~`.
    Null(Source),
    /// Accessing a nonexistent node via the Index trait returns `BadValue`. This
    /// simplifies error handling in the calling code. Invalid type conversion also
    /// returns `BadValue`.
    BadValue,
}

pub type Array = Vec<MarkedYaml>;

#[cfg(not(feature = "preserve_order"))]
pub type Hash = BTreeMap<String, MarkedYaml>;
#[cfg(feature = "preserve_order")]
pub type Hash = ::linked_hash_map::LinkedHashMap<String, MarkedYaml>;

pub struct MarkedYamlLoader {
    docs: Vec<MarkedYaml>,
    // states
    // (current node, anchor_id) tuple
    doc_stack: Vec<(MarkedYaml, usize)>,
    key_stack: Vec<MarkedYaml>,
    anchor_map: BTreeMap<usize, MarkedYaml>,
    source: String,
}

impl MarkedEventReceiver for MarkedYamlLoader {
    fn on_event(&mut self, ev: &Event, mark: Marker) {
        let src = Source {
            file: self.source.clone(),
            start: mark,
        };

        // println!("EV {:?}", ev);
        match *ev {
            Event::DocumentStart => {
                // do nothing
            }
            Event::DocumentEnd => {
                match self.doc_stack.len() {
                    // empty document
                    0 => self.docs.push(MarkedYaml::BadValue),
                    1 => self.docs.push(self.doc_stack.pop().unwrap().0),
                    _ => unreachable!(),
                }
            }
            Event::SequenceStart(aid) => {
                self.doc_stack
                    .push((MarkedYaml::Array(Vec::new(), src), aid));
            }
            Event::SequenceEnd => {
                let node = self.doc_stack.pop().unwrap();
                self.insert_new_node(node);
            }
            Event::MappingStart(aid) => {
                self.doc_stack
                    .push((MarkedYaml::Hash(Hash::new(), src), aid));
                self.key_stack.push(MarkedYaml::BadValue);
            }
            Event::MappingEnd => {
                self.key_stack.pop().unwrap();
                let node = self.doc_stack.pop().unwrap();
                self.insert_new_node(node);
            }
            Event::Scalar(ref v, style, aid, ref tag) => {
                let node = if style != TScalarStyle::Plain {
                    MarkedYaml::String(v.clone(), src)
                } else if let Some(TokenType::Tag(ref handle, ref suffix)) = *tag {
                    // XXX tag:yaml.org,2002:
                    if handle == "!!" {
                        match suffix.as_ref() {
                            "bool" => {
                                // "true" or "false"
                                match v.parse::<bool>() {
                                    Err(_) => MarkedYaml::BadValue,
                                    Ok(v) => MarkedYaml::Boolean(v, src),
                                }
                            }
                            "int" => {
                                match v.parse::<i64>() {
                                    Err(_) => MarkedYaml::BadValue,
                                    Ok(v) => MarkedYaml::Integer(v, src),
                                }
                            }
                            "float" => {
                                match v.parse::<f64>() {
                                    Err(_) => MarkedYaml::BadValue,
                                    Ok(_) => MarkedYaml::Real(v.clone(), src),
                                }
                            }
                            "null" => {
                                match v.as_ref() {
                                    "~" | "null" => MarkedYaml::Null(src),
                                    _ => MarkedYaml::BadValue,
                                }
                            }
                            _ => MarkedYaml::String(v.clone(), src),
                        }
                    } else {
                        MarkedYaml::String(v.clone(), src)
                    }
                } else {
                    // Datatype is not specified, or unrecognized
                    MarkedYaml::from_str(v.as_ref(), src)
                };

                self.insert_new_node((node, aid));
            }
            Event::Alias(id) => {
                let n = match self.anchor_map.get(&id) {
                    Some(v) => v.clone(),
                    None => MarkedYaml::BadValue,
                };
                self.insert_new_node((n, 0));
            }
            _ => { /* ignore */ }
        }
        // println!("DOC {:?}", self.doc_stack);
    }
}

impl MarkedYamlLoader {
    fn insert_new_node(&mut self, node: (MarkedYaml, usize)) {
        // valid anchor id starts from 1
        if node.1 > 0 {
            self.anchor_map.insert(node.1, node.0.clone());
        }
        if self.doc_stack.is_empty() {
            self.doc_stack.push(node);
        } else {
            let parent = self.doc_stack.last_mut().unwrap();
            match *parent {
                (MarkedYaml::Array(ref mut v, _), _) => v.push(node.0),
                (MarkedYaml::Hash(ref mut h, _), _) => {
                    let mut cur_key = self.key_stack.last_mut().unwrap();
                    // current node is a key
                    if cur_key.is_badvalue() {
                        *cur_key = node.0;
                        // current node is a value
                    } else {
                        let mut newkey = MarkedYaml::BadValue;
                        mem::swap(&mut newkey, cur_key);

                        let yaml_value = newkey.as_str().expect("should be type string").0;
                        h.insert(String::from(yaml_value), node.0);
                    }
                }
                _ => unreachable!(),
            }
        }
    }

    pub fn load_from_source(filename: &str, source: &str) -> Result<Vec<MarkedYaml>, ScanError> {
        let mut loader = MarkedYamlLoader {
            docs: Vec::new(),
            doc_stack: Vec::new(),
            key_stack: Vec::new(),
            anchor_map: BTreeMap::new(),
            source: String::from(filename),
        };
        let mut parser = Parser::new(source.chars());
        try!(parser.load(&mut loader, true));
        Ok(loader.docs)
    }
}

macro_rules! define_as (
    ($name:ident, $t:ident, $yt:ident) => (
pub fn $name(&self) -> Option<($t, Source)> {
    match *self {
        MarkedYaml::$yt(v, ref src) => Some((v, src.clone())),
        _ => None
    }
}
    );
);

macro_rules! define_as_ref (
    ($name:ident, $t:ty, $yt:ident) => (
pub fn $name(&self) -> Option<($t, Source)> {
    match *self {
        MarkedYaml::$yt(ref v, ref src) => Some((v, src.clone())),
        _ => None
    }
}
    );
);

macro_rules! define_into (
    ($name:ident, $t:ty, $yt:ident) => (
pub fn $name(self) -> Option<($t, Source)> {
    match self {
        MarkedYaml::$yt(v, src) => Some((v, src)),
        _ => None
    }
}
    );
);

impl MarkedYaml {
    define_as!(as_bool, bool, Boolean);
    define_as!(as_i64, i64, Integer);

    define_as_ref!(as_str, &str, String);
    define_as_ref!(as_hash, &Hash, Hash);
    define_as_ref!(as_vec, &Array, Array);

    define_into!(into_bool, bool, Boolean);
    define_into!(into_i64, i64, Integer);
    define_into!(into_string, String, String);
    define_into!(into_hash, Hash, Hash);
    define_into!(into_vec, Array, Array);

    pub fn is_null(&self) -> bool {
        match *self {
            MarkedYaml::Null(_) => true,
            _ => false,
        }
    }

    pub fn is_badvalue(&self) -> bool {
        match *self {
            MarkedYaml::BadValue => true,
            _ => false,
        }
    }

    pub fn as_f64(&self) -> Option<(f64, Source)> {
        match *self {
            MarkedYaml::Real(ref v, ref src) => v.parse::<f64>().map(|v| (v, src.clone())).ok(),
            _ => None,
        }
    }

    pub fn into_f64(self) -> Option<(f64, Source)> {
        match self {
            MarkedYaml::Real(v, src) => v.parse::<f64>().map(|v| (v, src)).ok(),
            _ => None,
        }
    }
}

#[cfg_attr(feature = "clippy", allow(should_implement_trait))]
impl MarkedYaml {
    // Not implementing FromStr because there is no possibility of Error.
    // This function falls back to Yaml::String if nothing else matches.
    pub fn from_str(v: &str, src: Source) -> MarkedYaml {
        if v.starts_with("0x") {
            let n = i64::from_str_radix(&v[2..], 16);
            if n.is_ok() {
                return MarkedYaml::Integer(n.unwrap(), src);
            }
        }
        if v.starts_with("0o") {
            let n = i64::from_str_radix(&v[2..], 8);
            if n.is_ok() {
                return MarkedYaml::Integer(n.unwrap(), src);
            }
        }
        if v.starts_with('+') && v[1..].parse::<i64>().is_ok() {
            return MarkedYaml::Integer(v[1..].parse::<i64>().unwrap(), src);
        }
        match v {
            "~" | "null" => MarkedYaml::Null(src),
            "true" => MarkedYaml::Boolean(true, src),
            "false" => MarkedYaml::Boolean(false, src),
            _ if v.parse::<i64>().is_ok() => MarkedYaml::Integer(v.parse::<i64>().unwrap(), src),
            // try parsing as f64
            _ if v.parse::<f64>().is_ok() => MarkedYaml::Real(v.to_owned(), src),
            _ => MarkedYaml::String(v.to_owned(), src),
        }
    }
}

static BAD_VALUE: MarkedYaml = MarkedYaml::BadValue;

impl<'a> Index<&'a str> for MarkedYaml {
    type Output = MarkedYaml;

    fn index(&self, idx: &'a str) -> &MarkedYaml {
        let key = idx.to_owned();
        match self.as_hash() {
            Some((h, _)) => h.get(&key).unwrap_or(&BAD_VALUE),
            None => &BAD_VALUE,
        }
    }
}

impl Index<usize> for MarkedYaml {
    type Output = MarkedYaml;

    fn index(&self, idx: usize) -> &MarkedYaml {
        match self.as_vec() {
            Some((v, _)) => v.get(idx).unwrap_or(&BAD_VALUE),
            None => &BAD_VALUE,
        }
    }
}

impl IntoIterator for MarkedYaml {
    type Item = MarkedYaml;
    type IntoIter = MarkedYamlIter;

    fn into_iter(self) -> Self::IntoIter {
        MarkedYamlIter {
            yaml: self.into_vec()
                .map(|(v, _)| v)
                .unwrap_or_else(Vec::new)
                .into_iter(),
        }
    }
}

pub struct MarkedYamlIter {
    yaml: vec::IntoIter<MarkedYaml>,
}

impl Iterator for MarkedYamlIter {
    type Item = MarkedYaml;

    fn next(&mut self) -> Option<MarkedYaml> {
        self.yaml.next()
    }
}

impl Ord for MarkedYaml {
    fn cmp(&self, other: &Self) -> Ordering {
        use self::MarkedYaml::*;

        match (self, other) {
            (&Real(ref e1, _), &Real(ref e2, _)) => e1.cmp(&e2),
            (&Integer(ref e1, _), &Integer(ref e2, _)) => e1.cmp(&e2),
            (&String(ref e1, _), &String(ref e2, _)) => e1.cmp(&e2),
            (&Boolean(ref e1, _), &Boolean(ref e2, _)) => e1.cmp(&e2),
            (&Array(ref e1, _), &Array(ref e2, _)) => e1.cmp(&e2),
            (&Hash(ref e1, _), &Hash(ref e2, _)) => e1.cmp(&e2),
            (&Alias(ref e1, _), &Alias(ref e2, _)) => e1.cmp(&e2),
            (&Null(_), &Null(_)) => Ordering::Equal,
            _ => Ordering::Less,
        }
    }
}

impl PartialOrd for MarkedYaml {
    fn partial_cmp(&self, other: &MarkedYaml) -> Option<Ordering> {
        use self::MarkedYaml::*;

        match (self, other) {
            (&Real(ref e1, _), &Real(ref e2, _)) => Some(e1.cmp(&e2)),
            (&Integer(ref e1, _), &Integer(ref e2, _)) => Some(e1.cmp(&e2)),
            (&String(ref e1, _), &String(ref e2, _)) => Some(e1.cmp(&e2)),
            (&Boolean(ref e1, _), &Boolean(ref e2, _)) => Some(e1.cmp(&e2)),
            (&Array(ref e1, _), &Array(ref e2, _)) => Some(e1.cmp(&e2)),
            (&Hash(ref e1, _), &Hash(ref e2, _)) => Some(e1.cmp(&e2)),
            (&Alias(ref e1, _), &Alias(ref e2, _)) => Some(e1.cmp(&e2)),
            (&Null(_), &Null(_)) => Some(Ordering::Equal),
            _ => None,
        }
    }
}

#[cfg(test)]
mod test {
    use yaml::*;
    use super::*;

    #[test]
    fn test_coerce() {
        let s = "---
a: 1
b: 2.2
c: [1, 2]
";
        let out = MarkedYamlLoader::load_from_source("-", &s).unwrap();
        let doc = &out[0];
        assert_eq!(doc["a"].as_i64().unwrap().0, 1i64);
        assert_eq!(doc["b"].as_f64().unwrap().0, 2.2f64);
        assert_eq!(doc["c"][1].as_i64().unwrap().0, 2i64);
        assert!(doc["d"][0].is_badvalue());
    }

    #[test]
    fn test_empty_doc() {
        let s: String = "".to_owned();
        MarkedYamlLoader::load_from_source("-", &s).unwrap();
        let s: String = "---".to_owned();
        assert!(MarkedYamlLoader::load_from_source("-", &s).unwrap()[0].is_null());
    }

    #[test]
    fn test_parser() {
        let s: String = "
# comment
a0 bb: val
a1:
    b1: 4
    b2: d
a2: 4 # i'm comment
a3: [1, 2, 3]
a4:
    - - a1
      - a2
    - 2
a5: 'single_quoted'
a6: \"double_quoted\"
a7: 你好
"
                .to_owned();
        let out = MarkedYamlLoader::load_from_source("-", &s).unwrap();
        let doc = &out[0];
        assert_eq!(doc["a7"].as_str().unwrap().0, "你好");
    }

    #[test]
    fn test_multi_doc() {
        let s = "
'a scalar'
---
'a scalar'
---
'a scalar'
";
        let out = MarkedYamlLoader::load_from_source("-", &s).unwrap();
        assert_eq!(out.len(), 3);
    }

    #[test]
    fn test_anchor() {
        let s = "
a1: &DEFAULT
    b1: 4
    b2: d
a2: *DEFAULT
";
        let out = MarkedYamlLoader::load_from_source("-", &s).unwrap();
        let doc = &out[0];
        assert_eq!(doc["a2"]["b1"].as_i64().unwrap().0, 4);
    }

    #[test]
    fn test_bad_anchor() {
        let s = "
a1: &DEFAULT
    b1: 4
    b2: *DEFAULT
";
        let out = MarkedYamlLoader::load_from_source("-", &s).unwrap();
        let doc = &out[0];
        assert_eq!(doc["a1"]["b2"], MarkedYaml::BadValue);
    }

    #[test]
    fn test_github_27() {
        // https://github.com/chyh1990/yaml-rust/issues/27
        let s = "&a";
        let out = MarkedYamlLoader::load_from_source("-", &s).unwrap();
        let doc = &out[0];
        assert_eq!(doc.as_str().unwrap().0, "");
    }

    #[test]
    fn test_plain_datatype() {
        let s = "
- 'string'
- \"string\"
- string
- 123
- -321
- 1.23
- -1e4
- ~
- null
- true
- false
- !!str 0
- !!int 100
- !!float 2
- !!null ~
- !!bool true
- !!bool false
- 0xFF
# bad values
- !!int string
- !!float string
- !!bool null
- !!null val
- 0o77
- [ 0xF, 0xF ]
- +12345
- [ true, false ]
";
        let out = MarkedYamlLoader::load_from_source("-", &s).unwrap();
        let doc = &out[0];

        assert_eq!(doc[0].as_str().unwrap().0, "string");
        assert_eq!(doc[1].as_str().unwrap().0, "string");
        assert_eq!(doc[2].as_str().unwrap().0, "string");
        assert_eq!(doc[3].as_i64().unwrap().0, 123);
        assert_eq!(doc[4].as_i64().unwrap().0, -321);
        assert_eq!(doc[5].as_f64().unwrap().0, 1.23);
        assert_eq!(doc[6].as_f64().unwrap().0, -1e4);
        assert!(doc[7].is_null());
        assert!(doc[8].is_null());
        assert_eq!(doc[9].as_bool().unwrap().0, true);
        assert_eq!(doc[10].as_bool().unwrap().0, false);
        assert_eq!(doc[11].as_str().unwrap().0, "0");
        assert_eq!(doc[12].as_i64().unwrap().0, 100);
        assert_eq!(doc[13].as_f64().unwrap().0, 2.0);
        assert!(doc[14].is_null());
        assert_eq!(doc[15].as_bool().unwrap().0, true);
        assert_eq!(doc[16].as_bool().unwrap().0, false);
        assert_eq!(doc[17].as_i64().unwrap().0, 255);
        assert!(doc[18].is_badvalue());
        assert!(doc[19].is_badvalue());
        assert!(doc[20].is_badvalue());
        assert!(doc[21].is_badvalue());
        assert_eq!(doc[22].as_i64().unwrap().0, 63);
        assert_eq!(doc[23][0].as_i64().unwrap().0, 15);
        assert_eq!(doc[23][1].as_i64().unwrap().0, 15);
        assert_eq!(doc[24].as_i64().unwrap().0, 12345);
        assert!(doc[25][0].as_bool().unwrap().0);
        assert!(!doc[25][1].as_bool().unwrap().0);
    }

    #[test]
    fn test_bad_hypen() {
        // See: https://github.com/chyh1990/yaml-rust/issues/23
        let s = "{-";
        assert!(MarkedYamlLoader::load_from_source("-", &s).is_err());
    }

    #[test]
    fn test_bad_docstart() {

        // FIXME: these are hardcoded by looking at the assertion failures... :(
        let src1 = Source {
            file: "-".into(),
            start: Marker {
                index: 0,
                line: 1,
                col: 0,
            },
        };
        let src2 = Source {
            file: "-".into(),
            start: Marker {
                index: 24,
                line: 2,
                col: 0,
            },
        };
        let src3 = Source {
            file: "-".into(),
            start: Marker {
                index: 0,
                line: 1,
                col: 0,
            },
        };

        assert!(MarkedYamlLoader::load_from_source("-", "---This used to cause an infinite loop")
                    .is_ok());
        assert_eq!(MarkedYamlLoader::load_from_source("-", "----"),
                   Ok(vec![MarkedYaml::String(String::from("----"), src1)]));
        assert_eq!(MarkedYamlLoader::load_from_source("-", "--- #here goes a comment"),
                   Ok(vec![MarkedYaml::Null(src2)]));
        assert_eq!(MarkedYamlLoader::load_from_source("-", "---- #here goes a comment"),
                   Ok(vec![MarkedYaml::String(String::from("----"), src3)]));
    }

    #[test]
    fn test_plain_datatype_with_into_methods() {
        let s = "
- 'string'
- \"string\"
- string
- 123
- -321
- 1.23
- -1e4
- true
- false
- !!str 0
- !!int 100
- !!float 2
- !!bool true
- !!bool false
- 0xFF
- 0o77
- +12345
";
        let mut out = MarkedYamlLoader::load_from_source("-", &s)
            .unwrap()
            .into_iter();
        let mut doc = out.next().unwrap().into_iter();

        assert_eq!(doc.next().unwrap().into_string().unwrap().0, "string");
        assert_eq!(doc.next().unwrap().into_string().unwrap().0, "string");
        assert_eq!(doc.next().unwrap().into_string().unwrap().0, "string");
        assert_eq!(doc.next().unwrap().into_i64().unwrap().0, 123);
        assert_eq!(doc.next().unwrap().into_i64().unwrap().0, -321);
        assert_eq!(doc.next().unwrap().into_f64().unwrap().0, 1.23);
        assert_eq!(doc.next().unwrap().into_f64().unwrap().0, -1e4);
        assert_eq!(doc.next().unwrap().into_bool().unwrap().0, true);
        assert_eq!(doc.next().unwrap().into_bool().unwrap().0, false);
        assert_eq!(doc.next().unwrap().into_string().unwrap().0, "0");
        assert_eq!(doc.next().unwrap().into_i64().unwrap().0, 100);
        assert_eq!(doc.next().unwrap().into_f64().unwrap().0, 2.0);
        assert_eq!(doc.next().unwrap().into_bool().unwrap().0, true);
        assert_eq!(doc.next().unwrap().into_bool().unwrap().0, false);
        assert_eq!(doc.next().unwrap().into_i64().unwrap().0, 255);
        assert_eq!(doc.next().unwrap().into_i64().unwrap().0, 63);
        assert_eq!(doc.next().unwrap().into_i64().unwrap().0, 12345);
    }
}
