#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstddef>
#include <cstdio>
#include <format>
#include <initializer_list>
#include <iostream>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <utility>
#include <variant>
#include <vector>

template <typename T> class stringuisher {
public:
  std::string operator()(const T &v) const { return std::to_string(v); }
};

template <typename T> std::string stringify(const T &v) {
  return stringuisher<T>()(v);
}

enum class action_t { shift, reduce, accept };

template <> class stringuisher<action_t> {
public:
  std::string operator()(const action_t &act) {
    switch (act) {
      using enum action_t;
    case shift:
      return "s";
    case reduce:
      return "r";
    case accept:
      return "acc";
    }
  }
};

enum class special_symbol_t { start, end };

template <typename term_t, typename nterm_t, bool nonterm = false>
struct symbol_t {
  std::variant<term_t, nterm_t, special_symbol_t> data;
  symbol_t() {}
  symbol_t(const term_t &t) : data(t) {
    static_assert(!nonterm,
                  "non-terminal symbol cannot be initialized terminal symbol.");
  }
  symbol_t(const nterm_t &t) : data(t) {}
  symbol_t(const special_symbol_t &t) : data(t) {}

  symbol_t(const symbol_t<term_t, nterm_t, true> &s) : data(s.data) {}

  bool operator<(const symbol_t &b) const { return this->data < b.data; }

  bool operator==(const symbol_t<term_t, nterm_t, true> &s) const {
    return this->data == s.data;
  }

  bool operator==(const symbol_t<term_t, nterm_t, false> &s) const {
    return this->data == s.data;
  }

  bool operator==(const special_symbol_t &s) const {
    if (this->data.index() == 2) {
      return std::get<2>(this->data) == s;
    }
    return false;
  }

  bool is_terminal() const { return data.index() == 0; }

  bool is_nonterminal() const { return data.index() == 1; }
};

template <typename term_t, typename nterm_t>
symbol_t<term_t, nterm_t, true>
cast_nonterminal(const symbol_t<term_t, nterm_t> &s) {
  return std::get<1>(s.data);
}

template <typename term_t, typename nterm_t>
class stringuisher<symbol_t<term_t, nterm_t>> {
public:
  std::string operator()(const symbol_t<term_t, nterm_t> &s) {
    auto data = s.data;
    if (data.index() == 0) {
      return stringify(std::get<0>(data));
    }
    if (data.index() == 1) {
      return stringify(std::get<1>(data));
    }
    switch (std::get<2>(data)) {
      using enum special_symbol_t;
    case start:
      return "^";
    case end:
      return "$";
    }
  }
};

template <typename term_t, typename nterm_t>
class stringuisher<symbol_t<term_t, nterm_t, true>> {
public:
  std::string operator()(const symbol_t<term_t, nterm_t> &s) {
    auto data = s.data;
    if (data.index() == 0) {
      return stringify(std::get<0>(data));
    }
    if (data.index() == 1) {
      return stringify(std::get<1>(data));
    }
    switch (std::get<2>(data)) {
      using enum special_symbol_t;
    case start:
      return "^";
    case end:
      return "$";
    }
  }
};

template <typename term_t, typename nterm_t> struct lr0table_t {
  using proc_t = std::pair<action_t, size_t>;
  std::vector<std::map<symbol_t<term_t, nterm_t>, proc_t>> action_table;
  std::vector<std::map<symbol_t<term_t, nterm_t, true>, size_t>> goto_table;
};

template <typename term_t, typename nterm_t>
class stringuisher<lr0table_t<term_t, nterm_t>> {
public:
  std::string operator()(const lr0table_t<term_t, nterm_t> &tbl) {
    size_t size = std::max(tbl.action_table.size(), tbl.goto_table.size());
    size_t width = std::log10(size) + 4;
    std::string res = std::format("{:^{}}", " ", width);
    std::vector<symbol_t<term_t, nterm_t>> symbols;
    for (auto &&e : tbl.action_table) {
      for (auto &&[s, proc] : e) {
        if (std::ranges::find(symbols, s) == symbols.end()) {
          symbols.push_back(s);
          res += std::format("{:^{}}", stringify(s), width);
        }
      }
    }
    for (auto &&e : tbl.goto_table) {
      for (auto &&[s, i] : e) {
        if (std::ranges::find(symbols, s) == symbols.end()) {
          symbols.push_back(s);
          res += std::format("{:^{}}", stringify(s), width);
        }
      }
    }
    res += "\n";

    auto act2str = [](const std::pair<action_t, size_t> &p) {
      return std::format("{}{}", stringify(p.first), p.second);
    };

    for (size_t i = 0; i < size; i++) {
      res += std::format("{:^{}}", i, width);
      for (auto &&s : symbols) {
        if (s.is_nonterminal()) {
          if (tbl.goto_table[i].contains(cast_nonterminal(s))) {
            res += std::format(
                "{:^{}}", tbl.goto_table[i].at(cast_nonterminal(s)), width);
          } else {
            res += std::format("{:^{}}", " ", width);
          }
        } else {
          if (tbl.action_table[i].contains(s)) {
            res += std::format("{:^{}}", act2str(tbl.action_table[i].at(s)),
                               width);
          } else {
            res += std::format("{:^{}}", " ", width);
          }
        }
      }
      res += "\n";
    }

    return res;
  }
};

template <typename term_t, typename nterm_t> struct rule_t {
  using prod_t = symbol_t<term_t, nterm_t, true>;
  prod_t product;
  using recipe_t = std::vector<symbol_t<term_t, nterm_t>>;
  recipe_t recipe;

  rule_t() {}

  rule_t(const prod_t &product, const recipe_t &recipe)
      : product(product), recipe(recipe) {}

  bool operator==(const rule_t &b) const {
    return (this->product == b.product) && (this->recipe == b.recipe);
  }

  bool operator<(const rule_t &b) const {
    if (this->product == b.product) {
      if (this->recipe.size() == this->recipe.size()) {
        for (size_t i = 0; i < std::min(this->recipe.size(), b.recipe.size());
             i++) {
          if (!(this->recipe.at(i) == b.recipe.at(i))) {
            return this->recipe.at(i) < b.recipe.at(i);
          }
        }
        return false;
      }
      return this->recipe.size() < b.recipe.size();
    }
    return this->product < b.product;
  }
};

template <typename term_t, typename nterm_t>
class stringuisher<rule_t<term_t, nterm_t>> {
public:
  std::string operator()(const rule_t<term_t, nterm_t> &rule) {
    std::string res = std::format("{} -> ", stringify(rule.product));
    for (auto &&s : rule.recipe) {
      res += std::format("{} ", stringify(s));
    }
    return res;
  }
};

template <typename term_t, typename nterm_t> struct lr0item_t {
  using rule_t = rule_t<term_t, nterm_t>;
  rule_t rule;
  size_t cursor = 0;

  lr0item_t(const rule_t &rule) : rule(rule) {}
  lr0item_t(const rule_t &rule, size_t cursor) : rule(rule), cursor(cursor) {}
  std::optional<symbol_t<term_t, nterm_t>> get_reading() const {
    if (cursor >= rule.recipe.size()) {
      return std::nullopt;
    }
    return rule.recipe.at(cursor);
  }

  lr0item_t get_next() const { return lr0item_t(rule, cursor + 1); }

  bool is_end() const { return cursor == rule.recipe.size(); }

  bool operator==(const lr0item_t &b) const {
    return this->rule == b.rule && this->cursor == b.cursor;
  }

  bool operator<(const lr0item_t &b) const {
    if (this->rule == b.rule) {
      return this->cursor < b.cursor;
    }
    return this->rule < b.rule;
  }
};

template <typename term_t, typename nterm_t> struct lr1item_t {
  using _lr0item_t = lr0item_t<term_t, nterm_t>;
  _lr0item_t lr0item;
  std::set<symbol_t<term_t, nterm_t>> aheads;

  lr1item_t(const _lr0item_t& item, const decltype(aheads)& aheads = {}) : lr0item(item), aheads(aheads) {}
  std::optional<symbol_t<term_t, nterm_t>> get_reading() const {
    return lr0item.get_reading();
  }

  lr1item_t get_next() const { return lr1item_t(lr0item.get_next(), aheads); }

  bool is_end() const { return lr0item.is_end(); }

  bool operator==(const lr1item_t &b) const {
    return this->lr0item == b.lr0item && this->aheads == b.aheads;
  }

  bool operator<(const lr1item_t &b) const {
    if (this->lr0item != b.lr0item) {
      return this->lr0item < b.lr0item;
    }
    return this->aheads < b.aheads;
  }
};

template <typename term_t, typename nterm_t>
class stringuisher<lr0item_t<term_t, nterm_t>> {
public:
  std::string operator()(const lr0item_t<term_t, nterm_t> &item) {
    std::string res = std::format("{} -> ", stringify(item.rule.product));
    for (size_t i = 0; i < item.rule.recipe.size(); i++) {
      if (i == item.cursor) {
        res += ".";
      }
      res += std::format("{} ", stringify(item.rule.recipe[i]));
    }
    if (item.cursor == (item.rule.recipe.size())) {
      res += ".";
    }
    return res;
  }
};

template <typename term_t, typename nterm_t>
class stringuisher<std::set<lr0item_t<term_t, nterm_t>>> {
public:
  std::string operator()(const std::set<lr0item_t<term_t, nterm_t>> &items) {
    std::string res = "{ \n";
    for (auto &&item : items) {
      res += std::format("  {}\n", stringify(item));
    }
    res += "}\n";
    return res;
  }
};

template <typename term_t, typename nterm_t> struct grammar_t {
  using _rule_t = rule_t<term_t, nterm_t>;
  using _symbol_t = symbol_t<term_t, nterm_t>;
  using _lr0item_t = lr0item_t<term_t, nterm_t>;
  using _lr1item_t = lr1item_t<term_t, nterm_t>;
  std::set<_rule_t> rules;

  void add_rule(const _rule_t::prod_t &p, const _rule_t::recipe_t &r) {
    rules.emplace(p, r);
  }

  std::set<_symbol_t> first(const _symbol_t &p) {
    std::set<_symbol_t> flag;
    return first_impl(p, flag);
  }

  std::set<_symbol_t> follow(const _symbol_t &s) {
    std::set<_symbol_t> res = {}, tobe = {s}, done = {};
    while (!tobe.empty()) {
      auto t = *tobe.begin();
      done.insert(t);
      if (t == special_symbol_t::start) {
        res.insert(special_symbol_t::end);
      } else {
        for (const _rule_t &rule : rules) {
          auto it = std::ranges::find(rule.recipe, t);
          if (it != rule.recipe.end()) {
            auto i = std::distance(it, rule.recipe.end());
            if (i == 1 && !done.contains(rule.product)) {
              tobe.insert(rule.product);
            } else {
              auto S = first(*(it + 1));
              res.insert(S.begin(), S.end());
            }
          }
        }
      }
      tobe.erase(std::ranges::find(tobe, t));
    }
    return res;
  }

  void set_start(const _symbol_t &s) {
    add_rule(special_symbol_t::start, {s, special_symbol_t::end});
  }

  std::set<_lr0item_t> lr0_closure(const _symbol_t &s) const {
    if (s.is_terminal()) {
      return {};
    }
    std::set<_lr0item_t> res = {};
    std::set<_symbol_t> tobe = {s}, done = {};
    while (!tobe.empty()) {
      auto t = *tobe.begin();
      for (auto &&rule : rules) {
        if (rule.product == t && !rule.recipe.empty()) {
          res.emplace(rule);
          if (!done.contains(rule.recipe[0])) {
            tobe.insert(rule.recipe[0]);
          }
        }
      }
      tobe.erase(t);
      done.insert(t);
    }
    return res;
  }

  std::set<_lr0item_t> lr0_closure(const _lr0item_t &t) const {
    auto s = t.get_reading();
    if (!s.has_value()) {
      return {};
    }
    auto res = lr0_closure(s.value());
    res.insert(t);
    return res;
  }

  std::set<_lr0item_t> get_start() const {
    std::set<_lr0item_t> res;
    for (const _rule_t &rule : rules) {
      if (rule.product == special_symbol_t::start) {
        res.emplace(rule);
      }
    }
    return res;
  }

  std::set<_lr0item_t> get_start_lr0() const {
    return lr0_closure(special_symbol_t::start);
  }

  std::set<_symbol_t> next_symbols(const std::set<_lr0item_t> &lr0items) const {
    std::set<_symbol_t> res{};
    for (auto &&lr0item : lr0items) {
      auto s = lr0item.get_reading();
      if (s.has_value())
        res.insert(s.value());
    }
    return res;
  }

  std::set<_lr0item_t> next_lr0items(const std::set<_lr0item_t> &lr0items,
                                     const _symbol_t &s) const {
    std::set<_lr0item_t> res{};
    for (auto &&lr0item : lr0items) {
      if (lr0item.get_reading() == s) {
        res.insert(lr0item.get_next());
      }
    }
    return res;
  }

  lr0table_t<term_t, nterm_t> gen_lr0table() const {
    lr0table_t<term_t, nterm_t> res;
    std::map<std::set<_lr0item_t>, size_t> mapstate;
    size_t used = 0;
    auto start = get_start_lr0();
    mapstate[start] = used++;
    std::set<std::set<_lr0item_t>> tobeprocs = {start}, done = {};
    std::vector<std::pair<size_t, size_t>> redmemo;
    std::set<symbol_t<term_t, nterm_t>> symbols_used = {};
    size_t acc_i = 0;
    while (!tobeprocs.empty()) {
      auto tobeproc = *tobeprocs.begin();
      std::cout << std::format("now id{} : {}\n", mapstate[tobeproc],
                               stringify(tobeproc));
      auto ss = next_symbols(tobeproc);
      symbols_used.insert(ss.begin(), ss.end());
      size_t now = mapstate[tobeproc];
      if (res.goto_table.size() < (now + 1)) {
        res.goto_table.resize(now + 1);
      }
      if (res.action_table.size() < (now + 1)) {
        res.action_table.resize(now + 1);
      }

      for (auto &&s : ss) {
        if (s == special_symbol_t::end) {
          res.action_table[now][s] = std::make_pair(action_t::accept, 0);
          continue;
        }
        auto S = next_lr0items(tobeproc, s);
        if (!mapstate.contains(S)) {
          mapstate[S] = used++;
        }
        if (!done.contains(S)) {
          tobeprocs.insert(S);
        }
        if (s.is_nonterminal()) {
          auto stricted = symbol_t<term_t, nterm_t, true>(std::get<1>(s.data));
          res.goto_table[now][stricted] = mapstate[S];
        } else {
          res.action_table[now][s] =
              std::make_pair(action_t::shift, mapstate[S]);
        }
      }
      for (auto &&item : tobeproc) {
        if (item.is_end()) {
          size_t ri =
              std::distance(rules.begin(), std::ranges::find(rules, item.rule));
          redmemo.emplace_back(now, ri);
        }
      }
      done.insert(tobeproc);
      tobeprocs.erase(std::ranges::find(tobeprocs, tobeproc));
      std::cout << stringify(res) << "\n";
    }
    for (auto &&[i, ri] : redmemo) {
      for (auto &&s : symbols_used) {
        res.action_table[i][s] = std::make_pair(action_t::reduce, ri);
      }
    }
    for (auto &&[state, id] : mapstate) {
      std::cout << std::format("id {} : {}\n", id, stringify(state));
    }
    return res;
  }

  std::set<_lr1item_t> lr1_closure(const std::set<_lr1item_t>& s) const {
    std::set<_lr1item_t> res = {};
  }

private:
  std::set<_symbol_t> first_impl(const _symbol_t &p,
                                 std::set<_symbol_t> &flag) {
    if (!p.is_nonterminal()) {
      return {p};
    }
    flag.insert(p);
    std::set<_symbol_t> res = {}, prev;
    do {
      prev = res;
      for (auto &&r : rules) {
        if (r.recipe.empty()) {
          continue;
        }
        auto e = r.recipe.at(0);
        if (r.product == p &&
            std::find(flag.begin(), flag.end(), e) == flag.end()) {
          auto S = first_impl(e, flag);
          res.insert(S.begin(), S.end());
        }
      }

    } while (res != prev);
    return res;
  }
};

enum class sym { E, T, Num };

template <> class stringuisher<char> {
public:
  std::string operator()(const char &ch) { return std::string({ch}); }
};

template <> class stringuisher<sym> {
public:
  std::string operator()(const sym &s) {
    switch (s) {
      using enum sym;
    case E:
      return "E";
    case T:
      return "T";
    case Num:
      return "Num";
    }
  }
};

int main() {
  auto g = grammar_t<char, sym>{};
  g.add_rule(sym::E, {sym::E, '+', sym::T});
  g.add_rule(sym::E, {sym::T});
  g.add_rule(sym::T, {sym::T, '*', 'i'});
  g.add_rule(sym::T, {'i'});
  auto s = g.first(sym::T);
  g.set_start(sym::E);
  auto lr0 = g.get_start_lr0();
  std::cout << stringify(lr0);
  auto lr0_ = g.next_lr0items(lr0, sym::E);
  std::cout << stringify(lr0_);
  auto tbl = g.gen_lr0table();
  std::cout << stringify(tbl);

  int i = 0;
  return 0;
}