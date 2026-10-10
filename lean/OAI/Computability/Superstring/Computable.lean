import OAI.Computability.Superstring.Arithmetic

namespace OAI

namespace Superstring.Computable
open BitCode
variable {α : Type} [DecidableEq α] [Inhabited α] [Coded α]

def nth (xs : List α) (i : ℕ) : α := xs[i]?.getD default
omit [DecidableEq α] in
@[fun_prop] theorem poly_nth {γ : Type} [Coded γ] {xs : γ → List α} {i : γ → ℕ}
    (hx : Poly xs) (hi : Poly i) : Poly (fun q => nth (xs q) (i q)) :=
  (BitCode.Poly.getD default).comp (hx.pair hi)

/-- All indices and loop counters below are explicitly represented unary data. -/
def occurs (T s : List α) (j : ℕ) : Bool :=
  lessEq (j + s.length) T.length && equal ((T.drop j).take s.length) s

def infixB (s T : List α) : Bool :=
  (List.range (T.length + 1)).any (fun j => occurs T s j)

def text (v : List α) (p : ℕ) (x : ℤ) : α :=
  nth v ((x % (p : ℤ)).toNat)

def matchesB (v : List α) (p : ℕ) (w : List α) : Bool :=
  (List.range w.length).all (fun i => equal (nth w i) (text v p i))

def blocks (v : List α) (p : ℕ) (s r : List α) (j : ℕ) : Bool :=
  less 0 j && less (j + s.length) r.length && occurs r s j &&
  ((List.range r.length).all (fun h =>
    !(less 0 h && less (h+1) r.length) ||
    equal (nth r h) (text v p ((h : ℤ) - j)))) &&
  !equal (nth r 0) (text v p (-(j : ℤ))) &&
  !equal (nth r (r.length-1)) (text v p (((r.length-1 : ℕ) : ℤ) - j))

def coefficient (v : List α) (p : ℕ) (s r : List α) : ℕ :=
  ((List.range (r.length + 1)).filter (fun j => blocks v p s r j)).length

omit [Inhabited α] in
@[fun_prop] theorem poly_occurs : Poly (fun q : List α × List α × ℕ => occurs q.1 q.2.1 q.2.2) := by
  unfold occurs
  fun_prop
omit [Inhabited α] in
@[fun_prop] theorem poly_infix : Poly (fun q : List α × List α => infixB q.1 q.2) := by
  unfold infixB
  exact BitCode.Poly.anyFn (p := fun q : (List α × List α) × ℕ => occurs q.1.2 q.1.1 q.2)
    (by fun_prop) (by fun_prop)
omit [DecidableEq α] in
@[fun_prop] theorem poly_text : Poly (fun q : List α × ℕ × ℤ => text q.1 q.2.1 q.2.2) := by
  unfold text
  exact (BitCode.Poly.getD default).comp (BitCode.Poly.fst.pair
    (BitCode.Poly.modIntNat.comp ((BitCode.Poly.snd.comp BitCode.Poly.snd).pair (BitCode.Poly.fst.comp BitCode.Poly.snd))))
@[fun_prop] theorem poly_matches : Poly (fun q : List α × ℕ × List α => matchesB q.1 q.2.1 q.2.2) := by
  unfold matchesB
  exact BitCode.Poly.allFn (p := fun q : (List α × ℕ × List α) × ℕ =>
    equal (nth q.1.2.2 q.2) (text q.1.1 q.1.2.1 q.2)) (by fun_prop) (by fun_prop)
@[fun_prop] theorem poly_blocks : Poly (fun q : List α × ℕ × List α × List α × ℕ =>
    blocks q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  have hi : Poly (fun q : (List α × ℕ × List α × List α × ℕ) × ℕ =>
      !(less 0 q.2 && less (q.2+1) q.1.2.2.2.1.length) ||
      equal (nth q.1.2.2.2.1 q.2) (text q.1.1 q.1.2.1 ((q.2 : ℤ) - q.1.2.2.2.2))) := by fun_prop
  have ha : Poly (fun q : List α × ℕ × List α × List α × ℕ =>
      (List.range q.2.2.2.1.length).all (fun h =>
        !(less 0 h && less (h+1) q.2.2.2.1.length) ||
        equal (nth q.2.2.2.1 h) (text q.1 q.2.1 ((h : ℤ) - q.2.2.2.2)))) :=
    BitCode.Poly.allFn hi (by fun_prop)
  unfold blocks
  fun_prop
@[fun_prop] theorem poly_coefficient : Poly (fun q : List α × ℕ × List α × List α =>
    coefficient q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold coefficient
  apply BitCode.Poly.length.comp
  exact BitCode.Poly.filterFn (p := fun q : (List α × ℕ × List α × List α) × ℕ =>
    blocks q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2) (by fun_prop) (by fun_prop)

omit [Inhabited α] [Coded α] in
theorem occurs_eq (T s : List α) (j : ℕ) : occurs T s j = true ↔ Counts.Occurs T s j := by
  simp only [occurs, Bool.and_eq_true, lessEq, equal, decide_eq_true_eq, Counts.Occurs]
  constructor
  · rintro ⟨hb,he⟩
    refine ⟨hb, fun i => ?_⟩
    have h := congrArg (fun w : List α => w[i.val]?) he
    simpa only [List.getElem?_take, ite_eq_left i.isLt, List.getElem?_drop] using h
  · rintro ⟨hb,he⟩
    refine ⟨hb, List.ext_getElem? (fun i => ?_)⟩
    by_cases hi : i < s.length
    · simpa only [List.getElem?_take, ite_eq_left hi, List.getElem?_drop] using he ⟨i,hi⟩
    · rw [List.getElem?_take, ite_eq_right hi, List.getElem?_eq_none_iff.mpr (by omega)]

omit [Inhabited α] [Coded α] in
theorem infix_eq (s T : List α) : infixB s T = true ↔ s <:+: T := by
  simp only [infixB, List.any_eq_true, List.mem_range, occurs_eq]
  constructor
  · rintro ⟨j,_,hj⟩; exact hj.infix
  · rintro ⟨a,b,rfl⟩
    refine ⟨a.length, by simp, ?_⟩
    apply (occurs_eq _ _ _).mp
    simp [occurs, lessEq, equal]

omit [DecidableEq α] [Coded α] in
theorem text_eq (v : List α) (p : ℕ) (x : ℤ) : text v p x = Counts.finiteText v p x := by
  simp only [text, nth, Counts.finiteText, List.getElem!_eq_getElem?_getD]

omit [Coded α] in
theorem matches_eq (v : List α) (p : ℕ) (w : List α) :
    matchesB v p w = true ↔ Counts.Matches (Counts.finiteText v p) w := by
  simp only [matchesB, List.all_eq_true, List.mem_range, Counts.Matches]
  constructor
  · intro h i
    have hh : nth w i.val = text v p i.val := of_decide_eq_true (h i.val i.isLt)
    rw [List.getElem?_eq_getElem i.isLt]
    exact congrArg some (by simpa only [nth, List.getElem?_eq_getElem i.isLt, Option.getD_some, text_eq] using hh)
  · intro h i hi
    apply decide_eq_true
    simpa only [nth, List.getElem?_eq_getElem hi, Option.getD_some, text_eq, Option.some.injEq] using h ⟨i,hi⟩

end Superstring.Computable

namespace Superstring.Computable
open BitCode
variable {α : Type} [DecidableEq α] [Inhabited α]

omit [DecidableEq α] in
theorem nth_eq_iff {r : List α} {i : ℕ} (hi : i < r.length) (a : α) :
    nth r i = a ↔ r[i]? = some a := by
  simp only [nth, List.getElem?_eq_getElem hi, Option.getD_some, Option.some.injEq]

theorem blocks_eq (v : List α) (p : ℕ) (s r : List α) (j : ℕ) :
    blocks v p s r j = true ↔ Counts.Block (Counts.finiteText v p) s r j := by
  have hi (h : ℕ) :
      (!(less 0 h && less (h+1) r.length) ||
        equal (nth r h) (text v p ((h : ℤ) - j))) = true ↔
      (0 < h → h+1 < r.length → nth r h = text v p ((h : ℤ) - j)) := by
    simp only [less, equal, Bool.or_eq_true, Bool.not_eq_true_eq_eq_false, Bool.and_eq_false_iff,
      decide_eq_false_iff_not, decide_eq_true_eq]
    tauto
  have ha : ((List.range r.length).all (fun h =>
      !(less 0 h && less (h+1) r.length) ||
      equal (nth r h) (text v p ((h : ℤ) - j)))) = true ↔
      ∀ h : Fin r.length, 0 < h.val → h.val + 1 < r.length →
        r[h.val]? = some (Counts.finiteText v p ((h.val : ℤ) - j)) := by
    simp only [List.all_eq_true, List.mem_range, hi]
    constructor
    · intro h i hi₀ hi₁
      exact (nth_eq_iff i.isLt _).mp (by simpa only [text_eq] using h i.val i.isLt hi₀ hi₁)
    · intro h i hilen hi₀ hi₁
      exact (nth_eq_iff hilen _).mpr (by simpa only [text_eq] using h ⟨i,hilen⟩ hi₀ hi₁)
  by_cases hj : 0 < j
  · by_cases hr : j + s.length < r.length
    · have hr0 : 0 < r.length := by omega
      have hr1 : r.length - 1 < r.length := by omega
      simp only [blocks, Bool.and_eq_true, ha, occurs_eq, Bool.not_eq_true_eq_eq_false]
      have hj' : 1 ≤ j := by omega
      simp only [less, equal, decide_eq_true_eq, decide_eq_false_iff_not,
        text_eq, nth_eq_iff hr0, nth_eq_iff hr1, Counts.Block, hj, hr, hj', true_and]
      tauto
    · simp [blocks, less, hr, Counts.Block]
  · have hj' : ¬1 ≤ j := by omega
    simp [blocks, less, hj, Counts.Block, hj']

end Superstring.Computable

namespace Superstring.Computable
open BitCode

theorem length_filter_range_card (n : ℕ) (b : ℕ → Bool) (P : ℕ → Prop) [DecidablePred P]
    (hb : ∀ i, b i = true ↔ P i) :
    ((List.range n).filter b).length = Fintype.card {i : Fin n // P i.val} := by
  let F := ((List.range n).filter b).toFinset
  have hm (i : ℕ) : i ∈ F ↔ i < n ∧ P i := by
    simp only [F, List.mem_toFinset, List.mem_filter, List.mem_range, hb]
  let e : {i : Fin n // P i.val} ≃ F := {
    toFun := fun i => ⟨i.val.val, (hm _).mpr ⟨i.val.isLt,i.property⟩⟩
    invFun := fun i => ⟨⟨i.val, ((hm _).mp i.property).1⟩, ((hm _).mp i.property).2⟩
    left_inv := fun i => by rfl
    right_inv := fun i => by rfl }
  have he := Fintype.card_congr e
  rw [Fintype.card_coe, List.toFinset_card_of_nodup (List.nodup_range.filter b)] at he
  exact he.symm

variable {α : Type} [DecidableEq α] [Inhabited α]

theorem coefficient_eq (v : List α) (p : ℕ) (s r : List α) :
    coefficient v p s r = Counts.coefficient (Counts.finiteText v p) s r :=
  length_filter_range_card _ _ _ (fun j => blocks_eq v p s r j)


def subwords (s : List α) : List (List α) := unique
  (((List.range (s.length+1)).map (fun i =>
    (List.range (s.length+1)).map (fun n => (s.drop i).take n))).flatten)

def vertices (S : List (List α)) : List (List α) := unique ([] :: (S.map subwords).flatten)

def required (S : List (List α)) : List (List α) := (unique S).filter (fun s =>
  !s.isEmpty && S.all (fun t => !infixB s t || equal t s))

def alphabet (S : List (List α)) : List α := unique S.flatten

omit [Inhabited α] in
theorem mem_subwords (w s : List α) : w ∈ subwords s ↔ w <:+: s := by
  simp only [subwords, mem_unique, List.mem_flatten, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨xs,⟨i,_,rfl⟩,hw⟩
    obtain ⟨n,_,rfl⟩ := List.mem_map.mp hw
    exact (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix
  · rintro ⟨a,b,rfl⟩
    refine ⟨_,⟨a.length, by simp, rfl⟩, ?_⟩
    apply List.mem_map.mpr
    refine ⟨w.length, List.mem_range.mpr (by simp; omega), ?_⟩
    simp

omit [Inhabited α] in
theorem vertices_eq (S : List (List α)) : (vertices S).toFinset = Input.vertices S := by
  ext w
  simp only [List.mem_toFinset, vertices, mem_unique, List.mem_cons, List.mem_flatten,
    List.mem_map, Input.mem_vertices]
  constructor
  · rintro (rfl | ⟨ws,⟨s,hs,rfl⟩,hw⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨s,hs,(mem_subwords _ _).mp hw⟩
  · rintro (rfl | ⟨s,hs,hw⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨subwords s,⟨s,hs,rfl⟩,(mem_subwords _ _).mpr hw⟩

omit [Inhabited α] in
theorem required_eq (S : List (List α)) : (required S).toFinset = Input.core S := by
  ext w
  simp only [required, List.mem_toFinset, List.mem_filter, mem_unique, Bool.and_eq_true,
    Bool.not_eq_true_eq_eq_false, List.isEmpty_eq_false_iff, List.all_eq_true, Bool.or_eq_true,
    equal, decide_eq_true_eq, Input.mem_core]
  have h (t : List α) : infixB w t = false ↔ ¬w <:+: t := by
    rw [Bool.eq_false_iff]
    exact not_congr (infix_eq _ _)
  simp only [h]
  constructor
  · rintro ⟨hw,hn,hh⟩
    exact ⟨hw,hn,fun t ht hwt => (hh t ht).resolve_left (not_not.mpr hwt)⟩
  · rintro ⟨hw,hn,hh⟩
    refine ⟨hw,hn,fun t ht => ?_⟩
    by_cases hwt : w <:+: t
    · exact Or.inr (hh t ht hwt)
    · exact Or.inl hwt

omit [Inhabited α] in
theorem alphabet_eq (S : List (List α)) : (alphabet S).toFinset = Input.alphabet S := by
  ext a
  simp only [alphabet, Input.alphabet, List.mem_toFinset, mem_unique]

end Superstring.Computable

namespace Superstring.Computable
open BitCode
variable {α : Type} [DecidableEq α] [Coded α]

@[fun_prop] theorem poly_subwords : Poly (subwords : List α → List (List α)) := by
  have hi : Poly (fun q : List α × ℕ =>
      (List.range (q.1.length+1)).map (fun n => (q.1.drop q.2).take n)) :=
    BitCode.Poly.mapFn (f := fun q : (List α × ℕ) × ℕ => (q.1.1.drop q.1.2).take q.2)
      (by fun_prop) (by fun_prop)
  unfold subwords
  exact BitCode.Poly.unique.comp (BitCode.Poly.flatten.comp (BitCode.Poly.mapFn hi (by fun_prop)))

@[fun_prop] theorem poly_vertices : Poly (vertices : List (List α) → List (List α)) := by
  unfold vertices
  have hm : Poly (fun S : List (List α) => (S.map subwords).flatten) :=
    BitCode.Poly.flatten.comp (BitCode.Poly.map (poly_subwords (α := α)))
  have hc : Poly (fun S : List (List α) => ([] : List α) :: (S.map subwords).flatten) := by
    exact (BitCode.Poly.cons (α := List α)).comp ((BitCode.Poly.const ([] : List α)).pair hm)
  exact BitCode.Poly.unique.comp hc

@[fun_prop] theorem poly_required : Poly (required : List (List α) → List (List α)) := by
  have ha : Poly (fun q : List (List α) × List α =>
      q.1.all (fun t => !infixB q.2 t || equal t q.2)) :=
    BitCode.Poly.allFn (p := fun q : (List (List α) × List α) × List α =>
      !infixB q.1.2 q.2 || equal q.2 q.1.2) (by fun_prop) (by fun_prop)
  unfold required
  exact BitCode.Poly.filterFn (p := fun q : List (List α) × List α =>
    !q.2.isEmpty && q.1.all (fun t => !infixB q.2 t || equal t q.2))
    (by fun_prop) (by fun_prop)

@[fun_prop] theorem poly_alphabet : Poly (alphabet : List (List α) → List α) := by
  unfold alphabet
  exact BitCode.Poly.unique.comp BitCode.Poly.flatten

end Superstring.Computable

namespace Superstring.Computable
open BitCode
variable {α : Type} [DecidableEq α]

abbrev DataCode (α : Type) := List (List α) × List (List α) × List α
abbrev Table (α : Type) := List (List α × ℕ)

def dataCode (S : List (List α)) : DataCode α := (vertices S, required S, alphabet S)

def decodeData (d : DataCode α) : Counts.Data α :=
  ⟨d.1.toFinset, d.2.1.toFinset, d.2.2.toFinset⟩

theorem decode_dataCode (S : List (List α)) : decodeData (dataCode S) = Input.data S := by
  simp only [decodeData, dataCode, vertices_eq, required_eq, alphabet_eq, Input.data]

/-- A finite association table; every stage is materialized before the next. -/
def lookup (t : Table α) (w : List α) : ℕ :=
  ((t.filter (fun e => equal e.1 w)).map Prod.snd).headD 0

theorem lookup_map (V : List (List α)) (f : List α → ℕ) (w : List α) :
    lookup (V.map (fun v => (v,f v))) w = if w ∈ V then f w else 0 := by
  induction V with
  | nil => simp [lookup]
  | cons v V ih =>
    by_cases hv : v = w
    · subst v; simp [lookup, equal]
    · simp only [List.map_cons, lookup, List.filter_cons, equal, decide_eq_true_eq,
        ite_eq_right hv, List.mem_cons] at *
      rw [ih]
      simp only [eq_comm (a := w) (b := v), hv, false_or]

theorem sum_map_finset {β : Type} [DecidableEq β] (xs : List β) (hn : xs.Nodup)
    (f : β → ℕ) : (xs.map f).sum = ∑ x ∈ xs.toFinset, f x := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := List.nodup_cons.mp hn
    have hnx : x ∉ xs.toFinset := by simpa only [List.mem_toFinset] using hh.1
    rw [List.map_cons, List.sum_cons, List.toFinset_cons, Finset.sum_insert hnx, ih hh.2]

theorem max_map_finset {β : Type} [DecidableEq β] (xs : List β) (f : β → ℕ) :
    (xs.map f).foldl Max.max 0 = xs.toFinset.sup f := by
  have h : ∀ a : ℕ, (xs.map f).foldl Max.max a = max a (xs.toFinset.sup f) := by
    intro a
    induction xs generalizing a with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.foldl_cons, ih,
        List.toFinset_cons, Finset.sup_insert, max_assoc]
  simpa using h 0

variable [Inhabited α]

def blocking (d : DataCode α) (t : Table α) (v : List α) (p : ℕ) (w : List α) : ℕ :=
  (d.1.map (fun r => coefficient v p w r * lookup t r)).sum

def rule (d : DataCode α) (t : Table α) (w v : List α) (p k : ℕ) : ℕ :=
  if less 0 p && less 0 k && !w.isEmpty && equal (w.length + k*p) v.length &&
      matchesB v p v && matchesB v p w then
    if less (blocking d t v p v) (lookup t v) then blocking d t v p w + k + 1 else 0
  else 0

def rulesFor (d : DataCode α) (t : Table α) (w v : List α) : ℕ :=
  ((List.range (v.length+1)).map (fun p =>
    ((List.range (v.length+1)).map (fun k => rule d t w v p k)).foldl Max.max 0)).foldl Max.max 0

def rules (d : DataCode α) (t : Table α) (w : List α) : ℕ :=
  (d.1.map (fun v => rulesFor d t w v)).foldl Max.max 0

def left (d : DataCode α) (t : Table α) (w : List α) : ℕ :=
  (d.2.2.map (fun c => if member (c::w) d.1 then lookup t (c::w) else 0)).sum

def right (d : DataCode α) (t : Table α) (w : List α) : ℕ :=
  (d.2.2.map (fun c => if member (w++[c]) d.1 then lookup t (w++[c]) else 0)).sum

def step (d : DataCode α) (t : Table α) (w : List α) : ℕ :=
  if member (w) d.1 && !w.isEmpty then
    max (if member (w) d.2.1 then 1 else 0)
      (max (left d t w) (max (right d t w) (rules d t w)))
  else 0

def tableStep (d : DataCode α) (t : Table α) : Table α := d.1.map (fun w => (w,step d t w))

theorem blocking_eq (d : DataCode α) (hd : d.1.Nodup) (t : Table α)
    (v : List α) (p : ℕ) (w : List α) :
    blocking d t v p w = Counts.blocking d.1.toFinset (Counts.finiteText v p) w (lookup t) := by
  simp only [blocking, sum_map_finset _ hd, coefficient_eq, Counts.blocking]

theorem rule_eq (d : DataCode α) (hd : d.1.Nodup) (t : Table α)
    (w v : List α) (p k : ℕ) :
    rule d t w v p k = (decodeData d).rule (lookup t) w v p k := by
  simp only [rule, Bool.and_eq_true, less, equal, decide_eq_true_eq,
    Bool.not_eq_true_eq_eq_false, List.isEmpty_eq_false_iff, matches_eq,
    blocking_eq d hd, decodeData, Counts.Data.rule]
  simp only [and_assoc]
  rfl

theorem rules_eq (d : DataCode α) (hd : d.1.Nodup) (t : Table α) (w : List α) :
    rules d t w = (decodeData d).rules (lookup t) w := by
  simp only [rules, rulesFor, max_map_finset, rule_eq d hd,
    List.toFinset_range, decodeData, Counts.Data.rules]

theorem step_eq (d : DataCode α) (hd : d.1.Nodup) (ha : d.2.2.Nodup)
    (t : Table α) (w : List α) : step d t w = (decodeData d).step (lookup t) w := by
  have hl : left d t w = (decodeData d).left (lookup t) w := by
    simp only [left, sum_map_finset _ ha, member_eq, Counts.Data.left,
      decodeData, List.mem_toFinset]
  have hr : right d t w = (decodeData d).right (lookup t) w := by
    simp only [right, sum_map_finset _ ha, member_eq, Counts.Data.right,
      decodeData, List.mem_toFinset]
  simp only [step, Bool.and_eq_true, member_eq, Bool.not_eq_true_eq_eq_false,
    List.isEmpty_eq_false_iff, hl, hr, rules_eq d hd, Counts.Data.step, decodeData,
    List.mem_toFinset]

end Superstring.Computable

namespace Superstring.Computable
open BitCode
variable {α : Type} [DecidableEq α] [Inhabited α] [Coded α]

omit [Inhabited α] in
@[fun_prop] theorem poly_dataCode : Poly (dataCode : List (List α) → DataCode α) := by
  unfold dataCode
  fun_prop

omit [Inhabited α] in
@[fun_prop] theorem poly_lookup : Poly (fun q : Table α × List α => lookup q.1 q.2) := by
  have hf : Poly (fun q : Table α × List α => q.1.filter (fun e => equal e.1 q.2)) :=
    BitCode.Poly.filterFn (p := fun q : (Table α × List α) × (List α × ℕ) => equal q.2.1 q.1.2)
      (by fun_prop) (by fun_prop)
  unfold lookup
  exact (BitCode.Poly.headD 0).comp ((BitCode.Poly.map BitCode.Poly.snd).comp hf)

@[fun_prop] theorem poly_blocking :
    Poly (fun q : DataCode α × Table α × List α × ℕ × List α =>
      blocking q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  unfold blocking
  exact BitCode.Poly.sum.comp (BitCode.Poly.mapFn
    (f := fun q : (DataCode α × Table α × List α × ℕ × List α) × List α =>
      coefficient q.1.2.2.1 q.1.2.2.2.1 q.1.2.2.2.2 q.2 * lookup q.1.2.1 q.2)
    (by fun_prop) (by fun_prop))

@[fun_prop] theorem poly_rule :
    Poly (fun q : DataCode α × Table α × List α × List α × ℕ × ℕ =>
      rule q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) := by
  unfold rule
  fun_prop

@[fun_prop] theorem poly_rulesFor :
    Poly (fun q : DataCode α × Table α × List α × List α =>
      rulesFor q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  have hi : Poly (fun q : (DataCode α × Table α × List α × List α) × ℕ =>
      ((List.range (q.1.2.2.2.length+1)).map (fun k =>
        rule q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2 k)).foldl Max.max 0) :=
    BitCode.Poly.maxFold.comp (BitCode.Poly.mapFn
      (f := fun q : ((DataCode α × Table α × List α × List α) × ℕ) × ℕ =>
        rule q.1.1.1 q.1.1.2.1 q.1.1.2.2.1 q.1.1.2.2.2 q.1.2 q.2)
      (by fun_prop) (by fun_prop))
  unfold rulesFor
  exact BitCode.Poly.maxFold.comp (BitCode.Poly.mapFn hi (by fun_prop))

@[fun_prop] theorem poly_rules : Poly (fun q : DataCode α × Table α × List α =>
    rules q.1 q.2.1 q.2.2) := by
  unfold rules
  exact BitCode.Poly.maxFold.comp (BitCode.Poly.mapFn
    (f := fun q : (DataCode α × Table α × List α) × List α =>
      rulesFor q.1.1 q.1.2.1 q.1.2.2 q.2) (by fun_prop) (by fun_prop))

omit [Inhabited α] in
@[fun_prop] theorem poly_left : Poly (fun q : DataCode α × Table α × List α =>
    left q.1 q.2.1 q.2.2) := by
  unfold left
  exact BitCode.Poly.sum.comp (BitCode.Poly.mapFn
    (f := fun q : (DataCode α × Table α × List α) × α =>
      if member (q.2::q.1.2.2) q.1.1.1 then lookup q.1.2.1 (q.2::q.1.2.2) else 0)
    (by fun_prop) (by fun_prop))

omit [Inhabited α] in
@[fun_prop] theorem poly_right : Poly (fun q : DataCode α × Table α × List α =>
    right q.1 q.2.1 q.2.2) := by
  unfold right
  exact BitCode.Poly.sum.comp (BitCode.Poly.mapFn
    (f := fun q : (DataCode α × Table α × List α) × α =>
      if member (q.1.2.2++[q.2]) q.1.1.1 then lookup q.1.2.1 (q.1.2.2++[q.2]) else 0)
    (by fun_prop) (by fun_prop))

@[fun_prop] theorem poly_step : Poly (fun q : DataCode α × Table α × List α =>
    step q.1 q.2.1 q.2.2) := by
  unfold step
  fun_prop

@[fun_prop] theorem poly_tableStep : Poly (fun q : DataCode α × Table α => tableStep q.1 q.2) := by
  unfold tableStep
  exact BitCode.Poly.mapFn (f := fun q : (DataCode α × Table α) × List α =>
    (q.2,step q.1.1 q.1.2 q.2)) (by fun_prop) (by fun_prop)

end Superstring.Computable

end OAI
