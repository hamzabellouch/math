import OAI.NumberTheory.Ostmann.Construction.WordRangeReplay

namespace OAI

/-! # Replaying the large-prime coprimalities at every reconstructed pivot -/

namespace Ostmann

open scoped Classical

structure HistoryPrimeCheck (σ V : Type*) where
  formula : HistoryFormula σ
  coordinate : V

noncomputable def HistoryPrimeCheck.Holds {σ V : Type*} (g : HistoryPrimeCheck σ V)
    (a : σ → ℤ) (prime : V → ℕ) : Prop :=
  (prime g.coordinate).Coprime (g.formula.integerValue a).natAbs

theorem HistoryFormula.integerValue_of_value {σ : Type*} (F : HistoryFormula σ)
    (a : σ → ℤ) (y : ℤ) (hy : F.value (fun i => (a i : ℚ)) = y) :
    F.integerValue a = y := by
  unfold integerValue
  rw [F.cleared.integer_value_cleared a y hy,
    Int.mul_ediv_cancel_left _ F.cleared.denominator_ne_zero]

inductive WordPrimeDecoration (V : Type*) : ℕ → Type _ where
  | leaf : WordPrimeDecoration V 0
  | node {n : ℕ} (coordinates : List V)
      (left right : WordPrimeDecoration V n) : WordPrimeDecoration V (n + 1)

noncomputable def WordPrimeDecoration.ValidAt {σ V : Type*} :
    {n : ℕ} → WordPrimeDecoration V n → WordTransferTemplate σ n →
      (σ → ℕ) → (V → ℕ) → FrequencyTree ℤ n → Prop
  | 0, .leaf, .leaf _, _, _, _ => True
  | n + 1, .node coordinates L R, .node d l r, x, prime, t =>
      let P := historyPivot (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x)
        t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      (∀ v ∈ coordinates, (prime v).Coprime P) ∧
        L.ValidAt l (Function.update x d.target P) prime t.2.1 ∧
        R.ValidAt r (Function.update x d.target P) prime t.2.2

noncomputable def WordPrimeDecoration.checks {σ V : Type*} :
    {n : ℕ} → WordPrimeDecoration V n → WordTransferTemplate σ n →
      (t : FrequencyTree ℤ n) → NonzeroInternalFrequencies n t →
        (σ → HistoryFormula σ) → List (HistoryPrimeCheck σ V)
  | 0, .leaf, .leaf _, _, _, _ => []
  | n + 1, .node coordinates L R, .node d l r, t, ht, env =>
      let step := wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ht.1
      let next := BranchingWordHistory.updatedFormulas step env
      coordinates.map (fun v => ⟨step.formula.bind env, v⟩) ++
        (L.checks l t.2.1 ht.2.1 next ++ R.checks r t.2.2 ht.2.2 next)

theorem wordTransfer_pivot_formula_value {σ : Type*} {n : ℕ}
    (d : WordTransferNode σ) (l r : WordTransferTemplate σ n) (x : σ → ℕ)
    (s v w : ℤ) (hs : s ≠ 0) (P : ℕ)
    (hp : ValidTransferNode (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x) s v w P)
    (env : σ → HistoryFormula σ) (a : σ → ℤ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ)) :
    ((wordTransferStep d s v w hs).formula.bind env).value (fun j => (a j : ℚ)) = (P : ℤ) := by
  have h := wordTransferUpdatedFormulas_nat d l r x s v w hs P hp env a henv d.target
  simpa only [BranchingWordHistory.updatedFormulas, wordTransferStep, Function.update_self,
    Int.cast_natCast] using h

/-- The tests use original prime values, unchanged by the pivot updates. -/
theorem WordPrimeDecoration.checks_iff {σ V : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (env : σ → HistoryFormula σ) (a : σ → ℤ) (x : σ → ℕ) (prime : V → ℕ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ))
    (hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t) :
    (∀ g ∈ D.checks template t ht env, g.Holds a prime) ↔ D.ValidAt template x prime t := by
  induction template generalizing env x with
  | leaf word => cases D; simp only [checks, List.not_mem_nil, false_implies, implies_true, ValidAt]
  | @node n d l r ihL ihR =>
    cases D with
    | node coordinates L R =>
      obtain ⟨P, hp, hvL, hvR⟩ := hv
      have hu := wordTransferUpdatedFormulas_nat d l r x _ _ _ ht.1 P hp env a henv
      have hpv := wordTransfer_pivot_formula_value d l r x _ _ _ ht.1 P hp env a henv
      have hpi := HistoryFormula.integerValue_of_value _ a (P : ℤ) hpv
      simp only [checks, List.forall_mem_append, List.forall_mem_map, ValidAt,
        hp.historyPivot_eq, HistoryPrimeCheck.Holds, hpi, Int.natAbs_natCast]
      exact and_congr Iff.rfl
        (and_congr (ihL L t.2.1 ht.2.1 _ _ hu hvL) (ihR R t.2.2 ht.2.2 _ _ hu hvR))

def WordPrimeDecoration.count {V : Type*} : {n : ℕ} → WordPrimeDecoration V n → ℕ
  | 0, .leaf => 0
  | _ + 1, .node coordinates L R => coordinates.length + L.count + R.count

theorem WordPrimeDecoration.checks_length {σ V : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    (D.checks template t ht env).length = D.count := by
  induction template generalizing env with
  | leaf word => cases D; rfl
  | node d l r ihL ihR =>
    cases D
    simp only [checks, count, List.length_append, List.length_map, ihL, ihR]
    omega

/-- Each check is attached to one of the actual pivot formulas, so it inherits
the already proved degree and small-denominator bounds. -/
theorem WordPrimeDecoration.check_formula_mem {σ V : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    ∀ g ∈ D.checks template t ht env,
      g.formula ∈ (template.branching t ht).pivotFormulas env := by
  induction template generalizing env with
  | leaf word => cases D; simp only [checks, List.not_mem_nil, false_implies, implies_true]
  | @node n d l r ihL ihR =>
    cases D with
    | node coordinates L R =>
      intro g hg
      change g ∈ coordinates.map _ ++ _ at hg
      change g.formula ∈ _ :: (_ ++ _)
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hg
        exact List.mem_cons_self
      · apply List.mem_cons_of_mem
        rcases List.mem_append.mp hg with hg | hg
        · exact List.mem_append_left _ (ihL L _ _ _ g hg)
        · exact List.mem_append_right _ (ihR R _ _ _ g hg)

end Ostmann

end OAI
