import Mathlib.Data.List.Lex
import Mathlib.Tactic

namespace OAI

/-!
# The finite path-pattern domain

A component is the list of its positive assigned-path amounts. An empty
component is an unused clique vertex. Components are ordered and identified
with their reversals, as in manuscript Lemma `finite:coverage`.
-/

namespace CycleClique.Construction
/-- Positive amount sequences with at most the indicated number of edges
and total amount at most the budget. -/
def amountSequences : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | e + 1, b => [] :: (List.range b).flatMap (fun q =>
      (amountSequences e (b - (q + 1))).map (fun p => (q + 1) :: p))

theorem mem_amountSequences {e b : ℕ} {p : List ℕ} :
    p ∈ amountSequences e b ↔ p.length ≤ e ∧ p.sum ≤ b ∧ ∀ a ∈ p, 0 < a := by
  induction e generalizing b p with
  | zero =>
    simp only [amountSequences, List.mem_singleton, Nat.le_zero]
    constructor
    · rintro rfl
      simp
    · rintro ⟨hp, _⟩
      simpa using hp
  | succ e ih =>
    cases p with
    | nil => simp [amountSequences]
    | cons a p =>
      constructor
      · intro h
        have hm : a :: p ∈ (List.range b).flatMap (fun q =>
            (amountSequences e (b - (q + 1))).map (fun p => (q + 1) :: p)) := by
          simpa only [amountSequences, List.mem_cons, List.cons_ne_nil, false_or] using h
        obtain ⟨q, hq, hm⟩ := List.mem_flatMap.mp hm
        obtain ⟨p', hp', heq⟩ := List.mem_map.mp hm
        rcases List.cons.inj heq with ⟨rfl, rfl⟩
        obtain ⟨hlen, hsum, hpos⟩ := ih.mp hp'
        have hqb : q < b := List.mem_range.mp hq
        refine ⟨by simp only [List.length_cons]; omega, ?_, ?_⟩
        · simp only [List.sum_cons]
          omega
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · omega
          · exact hpos a ha
      · rintro ⟨hlen, hsum, hpos⟩
        have ha : 0 < a := hpos a (by simp)
        have haeq : a - 1 + 1 = a := by omega
        have hsum' : a + p.sum ≤ b := by simpa using hsum
        apply List.mem_cons.mpr
        right
        apply List.mem_flatMap.mpr
        refine ⟨a - 1, List.mem_range.mpr (by omega), List.mem_map.mpr ?_⟩
        refine ⟨p, ih.mpr ⟨?_, ?_, ?_⟩, ?_⟩
        · simp only [List.length_cons] at hlen
          omega
        · omega
        · intro c hc
          exact hpos c (by simp [hc])
        · simp [haeq]

def LexLE (a b : List ℕ) : Prop := a = b ∨ List.Lex (· < ·) a b

instance (a b : List ℕ) : Decidable (LexLE a b) := by
  unfold LexLE
  infer_instance

/-- The compact checker's exact pattern recursion, including extensions of
components which do not themselves meet the ordering restriction. -/
def pathPatterns (t b : ℕ) (first : List ℕ := []) : List (List (List ℕ)) :=
  match t with
  | 0 => [[]]
  | t + 1 =>
    ((amountSequences t b).filter (fun p => decide (LexLE first p ∧ LexLE p p.reverse))).flatMap
      (fun p => (pathPatterns (t - p.length) (b - p.sum) p).map (fun P => p :: P))
termination_by t
decreasing_by omega

def patternCount (k t : ℕ) : ℕ := (pathPatterns t (k - t)).length

/-- Structurally recursive evaluator for the same domain. The fuel is
bounded by the number of remaining clique vertices. -/
def pathPatternsFuel : ℕ → ℕ → ℕ → List ℕ → List (List (List ℕ))
  | _, 0, _, _ => [[]]
  | 0, _ + 1, _, _ => []
  | f + 1, t + 1, b, first =>
    ((amountSequences t b).filter (fun p => decide (LexLE first p ∧ LexLE p p.reverse))).flatMap
      (fun p => (pathPatternsFuel f (t - p.length) (b - p.sum) p).map (fun P => p :: P))

theorem pathPatterns_eq_fuel {f t b : ℕ} {first : List ℕ} (h : t ≤ f) :
    pathPatterns t b first = pathPatternsFuel f t b first := by
  induction f generalizing t b first with
  | zero =>
    have : t = 0 := by omega
    subst t
    rw [pathPatterns, pathPatternsFuel]
  | succ f ih =>
    cases t with
    | zero => rw [pathPatterns, pathPatternsFuel]
    | succ t =>
      rw [pathPatterns, pathPatternsFuel]
      congr 1
      funext p
      rw [ih (show t - p.length ≤ f by omega)]

/-- Count components recursively without constructing a single long
flattened list. This keeps kernel reductions shallow. -/
def patternNumberFuel : ℕ → ℕ → ℕ → List ℕ → ℕ
  | _, 0, _, _ => 1
  | 0, _ + 1, _, _ => 0
  | f + 1, t + 1, b, first =>
    (((amountSequences t b).filter (fun p => decide (LexLE first p ∧ LexLE p p.reverse))).map
      (fun p => patternNumberFuel f (t - p.length) (b - p.sum) p)).sum

theorem pathPatternsFuel_length {f t b : ℕ} {first : List ℕ} :
    (pathPatternsFuel f t b first).length = patternNumberFuel f t b first := by
  induction f generalizing t b first with
  | zero => cases t <;> rfl
  | succ f ih =>
    cases t with
    | zero => rfl
    | succ t => simp only [pathPatternsFuel, patternNumberFuel, List.length_flatMap,
        List.length_map, ih]

/-- Sum over amount sequences by their short branching recursion, rather
than reducing a list whose length can approach the recursion-depth limit. -/
def amountSequenceSum : ℕ → ℕ → (List ℕ → ℕ) → ℕ
  | 0, _, F => F []
  | e + 1, b, F => F [] + ((List.range b).map (fun q =>
      amountSequenceSum e (b - (q + 1)) (fun p => F ((q + 1) :: p)))).sum

private theorem sum_flatMap_nat {α : Type*} (L : List α) (F : α → List ℕ) :
    (L.flatMap F).sum = (L.map (fun a => (F a).sum)).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]

theorem amountSequenceSum_eq {e b : ℕ} {F : List ℕ → ℕ} :
    amountSequenceSum e b F = ((amountSequences e b).map F).sum := by
  induction e generalizing b F with
  | zero => simp [amountSequenceSum, amountSequences]
  | succ e ih => simp only [amountSequenceSum, amountSequences, List.map_cons,
      List.sum_cons, List.map_flatMap, sum_flatMap_nat, List.map_map, ih, Function.comp_def]

private theorem sum_map_filter {α : Type*} (L : List α) (p : α → Bool) (F : α → ℕ) :
    ((L.filter p).map F).sum = (L.map (fun a => if p a then F a else 0)).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => cases h : p a <;> simp [h, ih]

def patternNumberShallow : ℕ → ℕ → ℕ → List ℕ → ℕ
  | _, 0, _, _ => 1
  | 0, _ + 1, _, _ => 0
  | f + 1, t + 1, b, first => amountSequenceSum t b (fun p =>
      if decide (LexLE first p ∧ LexLE p p.reverse)
      then patternNumberShallow f (t - p.length) (b - p.sum) p else 0)

theorem patternNumberFuel_eq_shallow {f t b : ℕ} {first : List ℕ} :
    patternNumberFuel f t b first = patternNumberShallow f t b first := by
  induction f generalizing t b first with
  | zero => cases t <;> rfl
  | succ f ih =>
    cases t with
    | zero => rfl
    | succ t =>
      simp only [patternNumberFuel, patternNumberShallow, amountSequenceSum_eq,
        sum_map_filter, ih]

def patternVertices (P : List (List ℕ)) : ℕ := (P.map (fun p => p.length + 1)).sum

def patternAmount (P : List (List ℕ)) : ℕ := (P.map List.sum).sum

def PatternValid : List ℕ → List (List ℕ) → Prop
  | _, [] => True
  | first, p :: P =>
    LexLE first p ∧ LexLE p p.reverse ∧ (∀ a ∈ p, 0 < a) ∧ PatternValid p P

/-- Exact coverage of the canonical domain, independently of the graph
obstruction checker. Each component uses one more clique vertex than edges. -/
theorem mem_pathPatterns {t b : ℕ} {first : List ℕ} {P : List (List ℕ)} :
    P ∈ pathPatterns t b first ↔
      patternVertices P = t ∧ patternAmount P ≤ b ∧ PatternValid first P := by
  induction t using Nat.strong_induction_on generalizing b first P with
  | h t ih =>
    cases t with
    | zero =>
      rw [pathPatterns]
      simp only [List.mem_singleton]
      constructor
      · rintro rfl
        simp [patternVertices, patternAmount, PatternValid]
      · rintro ⟨hv, _, _⟩
        cases P with
        | nil => rfl
        | cons p P => simp [patternVertices] at hv
    | succ t =>
      rw [pathPatterns]
      cases P with
      | nil => simp [patternVertices]
      | cons p P =>
        constructor
        · intro hm
          obtain ⟨p', hp', hm⟩ := List.mem_flatMap.mp hm
          obtain ⟨P', hP', heq⟩ := List.mem_map.mp hm
          have hp'eq := (List.cons.inj heq).1
          have hP'eq := (List.cons.inj heq).2
          subst p'
          subst P'
          obtain ⟨hpseq, hporder⟩ := List.mem_filter.mp hp'
          obtain ⟨hplen, hpsum, hppos⟩ := mem_amountSequences.mp hpseq
          have hrest := (ih (t - p.length) (by omega)).mp hP'
          have horder : LexLE first p ∧ LexLE p p.reverse := of_decide_eq_true hporder
          refine ⟨?_, ?_, horder.1, horder.2, hppos, hrest.2.2⟩
          · simp only [patternVertices, List.map_cons, List.sum_cons] at *
            omega
          · simp only [patternAmount, List.map_cons, List.sum_cons] at *
            omega
        · rintro ⟨hv, hb, hvalid⟩
          have hplen : p.length ≤ t := by
            simp only [patternVertices, List.map_cons, List.sum_cons] at hv
            omega
          have hpsum : p.sum ≤ b := by
            simp only [patternAmount, List.map_cons, List.sum_cons] at hb
            omega
          obtain ⟨horder, hreverse, hpos, htail⟩ := hvalid
          apply List.mem_flatMap.mpr
          refine ⟨p, List.mem_filter.mpr ⟨mem_amountSequences.mpr ⟨hplen, hpsum, hpos⟩,
            by simp [horder, hreverse]⟩, List.mem_map.mpr ?_⟩
          refine ⟨P, (ih (t - p.length) (by omega)).mpr ⟨?_, ?_, htail⟩, rfl⟩
          · simp only [patternVertices, List.map_cons, List.sum_cons] at hv ⊢
            omega
          · simp only [patternAmount, List.map_cons, List.sum_cons] at hb ⊢
            omega

end CycleClique.Construction

end OAI
