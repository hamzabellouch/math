import OAI.NumberTheory.Ostmann.Construction.WordTransferCounts

namespace OAI

/-! # The literal frequency and polynomial of every reconstructed Fourier leaf -/

namespace Ostmann

open scoped Classical

structure WeightedWordLeaf (σ : Type*) where
  positive : Bool
  frequency : ℤ
  formula : HistoryFormula σ

namespace WeightedWordLeaf

def flip {σ : Type*} (z : WeightedWordLeaf σ) : WeightedWordLeaf σ :=
  ⟨!z.positive, z.frequency, z.formula⟩

def toSignedFormula {σ : Type*} (z : WeightedWordLeaf σ) : Bool × HistoryFormula σ :=
  (z.positive, z.formula)

noncomputable def evaluate {σ : Type*} (a : σ → ℚ) (z : WeightedWordLeaf σ) : Bool × ℤ × ℚ :=
  (z.positive, z.frequency, z.formula.value a)

end WeightedWordLeaf

noncomputable def WordTransferTemplate.weightedLeaves {σ : Type*} :
    {n : ℕ} → WordTransferTemplate σ n → (t : FrequencyTree ℤ n) →
      NonzeroInternalFrequencies n t → (σ → HistoryFormula σ) → List (WeightedWordLeaf σ)
  | 0, .leaf word, v, _, env => [⟨true, v, HistoryFormula.listProduct (word.map env)⟩]
  | n + 1, .node d l r, t, ht, env =>
      let step := wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ht.1
      l.weightedLeaves t.2.1 ht.2.1 (BranchingWordHistory.updatedFormulas step env) ++
        (r.weightedLeaves t.2.2 ht.2.2 (BranchingWordHistory.updatedFormulas step env)).map WeightedWordLeaf.flip

theorem weightedWordLeaf_flip_projection {σ : Type*} (l : List (WeightedWordLeaf σ)) :
    (l.map WeightedWordLeaf.flip).map WeightedWordLeaf.toSignedFormula =
      (l.map WeightedWordLeaf.toSignedFormula).map BranchingWordHistory.flipSigned := by
  simp only [List.map_map]
  rfl

theorem WordTransferTemplate.weightedLeaves_projection {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    (template.weightedLeaves t hn env).map WeightedWordLeaf.toSignedFormula =
      (template.branching t hn).formulaLeaves env := by
  induction template generalizing env with
  | leaf word => rfl
  | @node n d l r hl hr =>
    simp only [weightedLeaves, branching, BranchingWordHistory.formulaLeaves,
      List.map_append, weightedWordLeaf_flip_projection, hl, hr]

theorem WordTransferTemplate.weightedLeaves_length {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    (template.weightedLeaves t hn env).length = 2 ^ n := by
  have he := congrArg List.length (template.weightedLeaves_projection t hn env)
  rw [List.length_map, template.branching_leafFormulas_length t hn env] at he
  exact he

/-- Preserve the actual leaf frequency as well as its sign and word value. -/
noncomputable def evaluatedTransferLeaf {σ : Type*}
    (z : (WordTransferState σ × ℤ) × Bool) : Bool × ℤ × ℚ :=
  (z.2, z.1.2, (wordTransferLeafValue z.1.1 : ℚ))

def flipEvaluatedLeaf (z : Bool × ℤ × ℚ) : Bool × ℤ × ℚ := (!z.1, z.2)

theorem weightedWordLeaf_flip_evaluate {σ : Type*} (a : σ → ℚ) (l : List (WeightedWordLeaf σ)) :
    (l.map WeightedWordLeaf.flip).map (WeightedWordLeaf.evaluate a) =
      (l.map (WeightedWordLeaf.evaluate a)).map flipEvaluatedLeaf := by
  simp only [List.map_map]
  rfl

theorem evaluatedTransferLeaf_flip {σ : Type*} (l : List ((WordTransferState σ × ℤ) × Bool)) :
    (l.map (fun z => (z.1, !z.2))).map evaluatedTransferLeaf =
      (l.map evaluatedTransferLeaf).map flipEvaluatedLeaf := by
  simp only [List.map_map]
  rfl

theorem WordTransferTemplate.weightedLeaves_value {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (x : σ → ℕ) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) (a : σ → ℚ)
    (henv : ∀ i, (env i).value a = (x i : ℚ))
    (hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t) :
    (template.weightedLeaves t hn env).map (WeightedWordLeaf.evaluate a) =
      (transferLeafList (wordTransferSystem σ) n (template.state x) t).map evaluatedTransferLeaf := by
  induction template generalizing x env with
  | leaf word =>
    simp only [weightedLeaves, transferLeafList, List.map_cons, List.map_nil,
      WeightedWordLeaf.evaluate, evaluatedTransferLeaf, WordTransferTemplate.state, wordTransferLeafValue]
    congr 2
    apply congrArg (fun q : ℚ => (t, q))
    have he := BranchingWordHistory.wordFormula_value word env a (fun i => (x i : ℤ)) (by
      intro i
      simpa only [Int.cast_natCast] using henv i)
    rw [he]
    clear hv he
    induction word with
    | nil => rfl
    | cons i word ih => simp only [List.map_cons, List.prod_cons, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, ih]
  | @node n d l r hl hr =>
    obtain ⟨P, hp, hvL, hvR⟩ := hv
    let step := wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) hn.1
    have hs : step.Valid (fun i => (x i : ℤ)) :=
      wordTransferStep_valid d l r x _ _ _ P hp
    have he : step.applyInteger (fun i => (x i : ℤ)) = fun i => (Function.update x d.target P i : ℤ) :=
      wordTransferStep_apply d l r x _ _ _ P hp
    have hu := BranchingWordHistory.updatedFormulas_value step env a (fun i => (x i : ℤ))
      (by intro i; simpa only [Int.cast_natCast] using henv i) hs
    rw [he] at hu
    have hu' : ∀ i, (BranchingWordHistory.updatedFormulas step env i).value a =
        (Function.update x d.target P i : ℚ) := by
      intro i
      simpa only [Int.cast_natCast] using hu i
    simp only [weightedLeaves, transferLeafList, List.map_append,
      weightedWordLeaf_flip_evaluate, evaluatedTransferLeaf_flip]
    rw [hp.historyPivot_eq, hl _ _ _ _ hu' hvL, hr _ _ _ _ hu' hvR]
    rfl

end Ostmann

end OAI
