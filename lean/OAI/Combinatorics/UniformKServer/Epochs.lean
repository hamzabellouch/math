import Mathlib
import OAI.Combinatorics.UniformKServer.Basic

namespace OAI

namespace UniformKServer
structure Entry (n k : ℕ) where
  position : Configuration n k
  moves : ℕ

def Covers {n k : ℕ} (e : Entry n k) (r : Fin n) : Prop := ∃ j, e.position j = r
instance {n k : ℕ} (e : Entry n k) (r : Fin n) : Decidable (Covers e r) :=
  inferInstanceAs (Decidable (∃ j, e.position j = r))

/-- Number of nodes in the full k-ary tree of depth m. -/
def treeBudget (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => 1 + k * treeBudget k m

@[simp] theorem treeBudget_zero (k : ℕ) : treeBudget k 0 = 1 := rfl
@[simp] theorem treeBudget_succ (k m : ℕ) :
    treeBudget k (m+1) = 1 + k * treeBudget k m := rfl

theorem treeBudget_pos (k m : ℕ) : 0 < treeBudget k m := by
  cases m <;> simp [treeBudget]

def expand {n k : ℕ} (M : ℕ) (r : Fin n) (e : Entry n k) : List (Entry n k) :=
  if Covers e r then [e]
  else if e.moves < M then
    (List.finRange k).map fun j => ⟨Function.update e.position j r, e.moves + 1⟩
  else []

def weight {n k : ℕ} (M : ℕ) (e : Entry n k) : ℕ := treeBudget k (M - e.moves)

def mass {n k : ℕ} (M : ℕ) (es : List (Entry n k)) : ℕ :=
  (es.map (weight M)).sum

def births {n k : ℕ} (M : ℕ) (r : Fin n) (e : Entry n k) : ℕ :=
  if Covers e r then 0 else if e.moves < M then k else 0

def futureMass {n k : ℕ} (M : ℕ) (es : List (Entry n k)) : ℕ :=
  (es.map fun e => weight M e - 1).sum

structure FilterState (n k : ℕ) where
  live : List (Entry n k)
  kept : List (Fin n)
  created : ℕ

def step {n k : ℕ} (M : ℕ) (s : FilterState n k) (r : Fin n) : FilterState n k :=
  if ∀ e ∈ s.live, Covers e r then s else
  { live := s.live.flatMap (expand M r)
    kept := s.kept ++ [r]
    created := s.created + (s.live.map (births M r)).sum }

def initial {n k : ℕ} (u : Configuration n k) : FilterState n k :=
  { live := [⟨u, 0⟩], kept := [], created := 1 }

def runFilter {n k : ℕ} (M : ℕ) (u : Configuration n k) (raw : List (Fin n)) :
    FilterState n k := raw.foldl (step M) (initial u)

/-- The exact source horizon H. -/
def horizon (k M : ℕ) : ℕ := ∑ i ∈ Finset.range (M+1), k^i

theorem treeBudget_eq_horizon (k M : ℕ) : treeBudget k M = horizon k M := by
  induction M with
  | zero => simp [horizon]
  | succ M ih =>
    simp only [treeBudget_succ, ih]
    unfold horizon
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [pow_zero, pow_succ', ← Finset.mul_sum]
    omega

@[simp] theorem mass_nil {n k : ℕ} (M : ℕ) : mass M ([] : List (Entry n k)) = 0 := rfl
@[simp] theorem mass_cons {n k : ℕ} (M : ℕ) (e : Entry n k) (es : List (Entry n k)) :
    mass M (e :: es) = weight M e + mass M es := rfl

@[simp] theorem mass_append {n k : ℕ} (M : ℕ) (a b : List (Entry n k)) :
    mass M (a ++ b) = mass M a + mass M b := by simp [mass]

theorem length_le_mass {n k : ℕ} (M : ℕ) (es : List (Entry n k)) :
    es.length ≤ mass M es := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have hp : 0 < weight M e := treeBudget_pos _ _
    simp only [List.length_cons, mass_cons]
    omega

theorem expand_valid {n k : ℕ} (M : ℕ) (r : Fin n) (e : Entry n k)
    (he : e.moves ≤ M) : ∀ e' ∈ expand M r e, e'.moves ≤ M := by
  unfold expand
  split_ifs with hc hm
  · simpa using he
  · intro e' he'
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp he'
    dsimp
    omega
  · simp

theorem mass_expand {n k : ℕ} (M : ℕ) (r : Fin n) (e : Entry n k)
    (he : e.moves ≤ M) :
    mass M (expand M r e) + (if Covers e r then 0 else 1) = weight M e := by
  unfold expand
  split_ifs with hc hm
  · simp [mass]
  · have hsub : M - e.moves = (M - (e.moves + 1)) + 1 := by omega
    simp [mass, weight, Function.comp_def, hsub, List.sum_replicate]; omega
  · have heq : e.moves = M := by omega
    simp [mass, weight, heq]


theorem futureMass_add_length {n k : ℕ} (M : ℕ) (es : List (Entry n k)) :
    futureMass M es + es.length = mass M es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have hp : 1 ≤ weight M e := treeBudget_pos _ _
    simp only [futureMass, List.map_cons, List.sum_cons, List.length_cons] at *
    simp only [mass_cons]
    omega

theorem futureMass_expand {n k : ℕ} (M : ℕ) (r : Fin n) (e : Entry n k)
    (he : e.moves ≤ M) :
    futureMass M (expand M r e) + births M r e = weight M e - 1 := by
  have hm := mass_expand M r e he
  have hf := futureMass_add_length M (expand M r e)
  by_cases hc : Covers e r
  · simp [expand, births, hc, futureMass]
  · by_cases hlt : e.moves < M
    · have hl : (expand M r e).length = k := by simp [expand, hc, hlt]
      simp only [hc, ↓reduceIte] at hm
      simp only [births, hc, hlt, ↓reduceIte]
      omega
    · have heq : e.moves = M := by omega
      simp [expand, births, hc, futureMass, weight, heq]

def misses {n k : ℕ} (r : Fin n) (es : List (Entry n k)) : ℕ :=
  (es.map fun e => if Covers e r then 0 else 1).sum

theorem misses_zero_iff {n k : ℕ} (r : Fin n) (es : List (Entry n k)) :
    misses r es = 0 ↔ ∀ e ∈ es, Covers e r := by
  induction es with
  | nil => simp [misses]
  | cons e es ih =>
    by_cases hc : Covers e r <;> simp_all [misses]

theorem mass_expansion {n k : ℕ} (M : ℕ) (r : Fin n) (es : List (Entry n k))
    (hvalid : ∀ e ∈ es, e.moves ≤ M) :
    mass M (es.flatMap (expand M r)) + misses r es = mass M es := by
  induction es with
  | nil => simp [misses]
  | cons e es ih =>
    have he : e.moves ≤ M := hvalid e (by simp)
    have hv : ∀ e ∈ es, e.moves ≤ M := fun e he => hvalid e (by simp [he])
    have hm := mass_expand M r e he
    have hi := ih hv
    simp only [List.flatMap_cons, mass_append, mass_cons]
    simp only [misses, List.map_cons, List.sum_cons]
    unfold misses at hi
    omega

@[simp] theorem futureMass_append {n k : ℕ} (M : ℕ) (a b : List (Entry n k)) :
    futureMass M (a ++ b) = futureMass M a + futureMass M b := by simp [futureMass]

theorem futureMass_expansion {n k : ℕ} (M : ℕ) (r : Fin n) (es : List (Entry n k))
    (hvalid : ∀ e ∈ es, e.moves ≤ M) :
    futureMass M (es.flatMap (expand M r)) + (es.map (births M r)).sum =
      futureMass M es := by
  induction es with
  | nil => simp [futureMass]
  | cons e es ih =>
    have he : e.moves ≤ M := hvalid e (by simp)
    have hv : ∀ e ∈ es, e.moves ≤ M := fun e he => hvalid e (by simp [he])
    have hm := futureMass_expand M r e he
    have hi := ih hv
    simp only [List.flatMap_cons, futureMass_append, List.map_cons, List.sum_cons]
    change _ = (weight M e - 1) + futureMass M es
    omega

def Good {n k : ℕ} (M B : ℕ) (s : FilterState n k) : Prop :=
  (∀ e ∈ s.live, e.moves ≤ M) ∧
  s.kept.length + mass M s.live ≤ B ∧
  s.created + futureMass M s.live = B

theorem step_good {n k : ℕ} (M B : ℕ) (s : FilterState n k) (r : Fin n)
    (hs : Good M B s) : Good M B (step M s r) := by
  unfold step
  split_ifs with hc
  · exact hs
  · rcases hs with ⟨hv, hb, hf⟩
    have hm := mass_expansion M r s.live hv
    have hfuture := futureMass_expansion M r s.live hv
    have hmiss : 0 < misses r s.live := by
      have hn : misses r s.live ≠ 0 := fun h => hc ((misses_zero_iff r s.live).mp h)
      exact Nat.pos_of_ne_zero hn
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      obtain ⟨old, hold, he⟩ := List.mem_flatMap.mp he
      exact expand_valid M r old (hv old hold) e he
    · dsimp
      simp only [List.length_append, List.length_singleton]
      omega
    · dsimp
      omega

theorem runFilter_good {n k : ℕ} (M : ℕ) (u : Configuration n k)
    (raw : List (Fin n)) : Good M (treeBudget k M) (runFilter M u raw) := by
  have hi : Good M (treeBudget k M) (initial u) := by
    refine ⟨?_, ?_, ?_⟩
    · simp [initial]
    · simp [initial, mass, weight]
    · have hp := treeBudget_pos k M
      dsimp [initial, futureMass, weight]
      simp only [Nat.sub_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
  have hfold : ∀ (rs : List (Fin n)) (s : FilterState n k),
      Good M (treeBudget k M) s → Good M (treeBudget k M) (rs.foldl (step M) s) := by
    intro rs
    induction rs with
    | nil => intro s hs; exact hs
    | cons r rs ih =>
      intro s hs
      exact ih (step M s r) (step_good M _ s r hs)
  exact hfold raw (initial u) hi

/-- Source Lemma `lem:filter`: all created entries, the live list, and the kept
word are bounded by H, for every raw finite prefix, even when the list empties.
The deterministic filter and bound do not inspect any random online trajectory. -/
theorem filter_bounds {n k : ℕ} (M : ℕ) (u : Configuration n k)
    (raw : List (Fin n)) :
    let s := runFilter M u raw
    s.created ≤ horizon k M ∧ s.live.length ≤ horizon k M ∧
      s.kept.length ≤ horizon k M := by
  dsimp
  obtain ⟨_, hb, hf⟩ := runFilter_good M u raw
  have hl := length_le_mass M (runFilter M u raw).live
  rw [treeBudget_eq_horizon] at hb hf
  omega

/-- The source's strongly lazy rule: a hit changes nothing; a miss chooses
exactly one label and counts one positive move. -/
def LazyStep {n k : ℕ} (e : Entry n k) (r : Fin n) (e' : Entry n k) : Prop :=
  if Covers e r then e' = e else
    ∃ j : Fin k, e' = ⟨Function.update e.position j r, e.moves + 1⟩

/-- Endpoints of complete strongly lazy paths, with no cap imposed in the relation. -/
inductive LazyPath {n k : ℕ} (u : Configuration n k) :
    List (Fin n) → Entry n k → Prop
  | nil : LazyPath u [] ⟨u, 0⟩
  | snoc {w : List (Fin n)} {e e' : Entry n k} {r : Fin n} :
      LazyPath u w e → LazyStep e r e' → LazyPath u (w ++ [r]) e'

@[simp] theorem lazyPath_nil_iff {n k : ℕ} (u : Configuration n k) (e : Entry n k) :
    LazyPath u [] e ↔ e = ⟨u, 0⟩ := by
  constructor
  · intro h
    generalize hw : ([] : List (Fin n)) = w at h
    cases h with
    | nil => rfl
    | snoc hp hs => simp at hw
  · rintro rfl
    exact LazyPath.nil

theorem lazyPath_snoc_iff {n k : ℕ} (u : Configuration n k)
    (w : List (Fin n)) (r : Fin n) (e' : Entry n k) :
    LazyPath u (w ++ [r]) e' ↔ ∃ e, LazyPath u w e ∧ LazyStep e r e' := by
  constructor
  · intro h
    generalize hw : w ++ [r] = wr at h
    cases h with
    | nil => simp at hw
    | @snoc w' e e' r' hp hs =>
      have hw' : w = w' ∧ r = r' := by simpa using hw
      rcases hw' with ⟨rfl, rfl⟩
      exact ⟨_, hp, hs⟩
  · rintro ⟨e, hp, hs⟩
    exact LazyPath.snoc hp hs

theorem lazyStep_moves_mono {n k : ℕ} {e e' : Entry n k} {r : Fin n}
    (h : LazyStep e r e') : e.moves ≤ e'.moves := by
  unfold LazyStep at h
  split_ifs at h with hc
  · subst e'; exact le_rfl
  · obtain ⟨j, rfl⟩ := h
    exact Nat.le_succ _

theorem mem_expand_iff {n k : ℕ} (M : ℕ) (r : Fin n) (e e' : Entry n k)
    (he : e.moves ≤ M) :
    e' ∈ expand M r e ↔ LazyStep e r e' ∧ e'.moves ≤ M := by
  by_cases hc : Covers e r
  · simp only [expand, LazyStep, hc, ↓reduceIte, List.mem_singleton]
    exact ⟨fun h => ⟨h, h ▸ he⟩, And.left⟩
  · by_cases hm : e.moves < M
    · simp only [expand, hc, ↓reduceIte, hm, List.mem_map, List.mem_finRange,
        true_and, LazyStep]
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨⟨j, rfl⟩, by dsimp; omega⟩
      · rintro ⟨⟨j, rfl⟩, _⟩
        exact ⟨j, rfl⟩
    · simp only [expand, hc, ↓reduceIte, hm, List.not_mem_nil, LazyStep,
        false_iff, not_and]
      rintro ⟨j, rfl⟩
      dsimp
      omega

/-- The representation invariant retains all capped paths, not just paths with
positive probability under a particular table. -/
def Represents {n k : ℕ} (M : ℕ) (u : Configuration n k)
    (s : FilterState n k) : Prop :=
  ∀ e, e ∈ s.live ↔ LazyPath u s.kept e ∧ e.moves ≤ M

theorem initial_represents {n k : ℕ} (M : ℕ) (u : Configuration n k) :
    Represents M u (initial u) := by
  intro e
  simp only [initial, List.mem_singleton, lazyPath_nil_iff]
  exact ⟨fun h => ⟨h, by rw [h]; exact Nat.zero_le _⟩, And.left⟩

theorem step_represents {n k : ℕ} (M : ℕ) (u : Configuration n k)
    (s : FilterState n k) (r : Fin n) (hs : Represents M u s) :
    Represents M u (step M s r) := by
  unfold step
  split_ifs with hc
  · exact hs
  · intro e'
    dsimp
    rw [List.mem_flatMap, lazyPath_snoc_iff]
    constructor
    · rintro ⟨e, he, he'⟩
      obtain ⟨hp, hm⟩ := (hs e).mp he
      obtain ⟨hstep, hm'⟩ := (mem_expand_iff M r e e' hm).mp he'
      exact ⟨⟨e, hp, hstep⟩, hm'⟩
    · rintro ⟨⟨e, hp, hstep⟩, hm'⟩
      have hm : e.moves ≤ M := (lazyStep_moves_mono hstep).trans hm'
      exact ⟨e, (hs e).mpr ⟨hp, hm⟩,
        (mem_expand_iff M r e e' hm).mpr ⟨hstep, hm'⟩⟩

theorem filter_represents {n k : ℕ} (M : ℕ) (u : Configuration n k)
    (raw : List (Fin n)) : Represents M u (runFilter M u raw) := by
  have hf : ∀ (rs : List (Fin n)) (s : FilterState n k),
      Represents M u s → Represents M u (rs.foldl (step M) s) := by
    intro rs
    induction rs with
    | nil => intro s hs; exact hs
    | cons r rs ih => intro s hs; exact ih _ (step_represents M u s r hs)
  exact hf raw _ (initial_represents M u)

theorem lazyStep_injective {n k : ℕ} {e e' : Entry n k} {r : Fin n}
    (hi : Function.Injective e.position) (hs : LazyStep e r e') :
    Function.Injective e'.position := by
  unfold LazyStep at hs
  split_ifs at hs with hc
  · subst e'; exact hi
  · obtain ⟨j, rfl⟩ := hs
    intro a b hab
    dsimp at hab
    by_cases ha : a = j
    · subst a
      by_cases hb : b = j
      · exact hb.symm
      · have heq : r = e.position b := by simpa [Function.update, hb] using hab
        exact False.elim (hc ⟨b, heq.symm⟩)
    · by_cases hb : b = j
      · subst b
        have heq : e.position a = r := by simpa [Function.update, ha] using hab
        exact False.elim (hc ⟨a, heq⟩)
      · apply hi
        simpa [Function.update, ha, hb] using hab

theorem lazyPath_injective {n k : ℕ} {u : Configuration n k}
    (hu : Function.Injective u) {w : List (Fin n)} {e : Entry n k}
    (hp : LazyPath u w e) : Function.Injective e.position := by
  induction hp with
  | nil => exact hu
  | snoc hp hs ih => exact lazyStep_injective ih hs

/-- Full deterministic content of the source's Universal Filter lemma. -/
theorem universal_filter {n k : ℕ} (M : ℕ) (u : Configuration n k)
    (hu : Function.Injective u) (raw : List (Fin n)) :
    let s := runFilter M u raw
    (∀ e, e ∈ s.live ↔ LazyPath u s.kept e ∧ e.moves ≤ M) ∧
    (∀ e ∈ s.live, Function.Injective e.position) ∧
    s.created ≤ horizon k M ∧ s.live.length ≤ horizon k M ∧
      s.kept.length ≤ horizon k M := by
  dsimp
  refine ⟨filter_represents M u raw, ?_, filter_bounds M u raw⟩
  intro e he
  exact lazyPath_injective hu ((filter_represents M u raw e).mp he).1

end UniformKServer



end OAI
