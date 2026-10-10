import OAI.NumberTheory.Ostmann.Construction.ExpandedScheduleState
import OAI.NumberTheory.Ostmann.Construction.WordTransferFourier
import OAI.NumberTheory.Ostmann.Construction.WordTransferGuardReplay

namespace OAI

namespace Ostmann

open scoped Classical

structure WordRange (σ : Type*) where
  word : List σ
  lower : ℝ
  upper : ℝ

structure HistoryRange (σ : Type*) where
  formula : HistoryFormula σ
  lower : ℝ
  upper : ℝ

noncomputable def WordRange.Holds {σ : Type*} (r : WordRange σ) (x : σ → ℕ) : Prop :=
  ((r.word.map x).prod : ℝ) ∈ Set.Icc r.lower r.upper

noncomputable def HistoryRange.Holds {σ : Type*} (r : HistoryRange σ) (a : σ → ℤ) : Prop :=
  r.formula.realValue a ∈ Set.Icc r.lower r.upper

noncomputable def WordRange.toHistory {σ : Type*} (r : WordRange σ)
    (env : σ → HistoryFormula σ) : HistoryRange σ :=
  ⟨HistoryFormula.listProduct (r.word.map env), r.lower, r.upper⟩

theorem WordRange.toHistory_holds {σ : Type*} (r : WordRange σ)
    (env : σ → HistoryFormula σ) (a : σ → ℤ) (x : σ → ℕ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ)) :
    (r.toHistory env).Holds a ↔ r.Holds x := by
  have hval := BranchingWordHistory.wordFormula_value r.word env (fun j => (a j : ℚ))
    (fun i => (x i : ℤ)) (fun i => by simpa only [Int.cast_natCast] using henv i)
  have hprod : (r.word.map (fun i => (x i : ℤ))).prod = ((r.word.map x).prod : ℤ) := by
    induction r.word with
    | nil => rfl
    | cons i is ih => simp only [List.map_cons, List.prod_cons, ih, Nat.cast_mul]
  rw [hprod] at hval
  have hreal : (HistoryFormula.listProduct (r.word.map env)).realValue a = ((r.word.map x).prod : ℝ) := by
    rw [HistoryFormula.realValue_ratCast, hval, Rat.cast_intCast, Int.cast_natCast]
  exact Iff.of_eq (congrArg (fun z : ℝ => z ∈ Set.Icc r.lower r.upper) hreal)

inductive WordRangeDecoration (σ : Type*) : ℕ → Type _ where
  | leaf (ranges : List (WordRange σ)) : WordRangeDecoration σ 0
  | node {n : ℕ} (ranges : List (WordRange σ))
      (left right : WordRangeDecoration σ n) : WordRangeDecoration σ (n + 1)

noncomputable def WordRangeDecoration.ValidAt {σ : Type*} :
    {n : ℕ} → WordRangeDecoration σ n → WordTransferTemplate σ n →
      (σ → ℕ) → FrequencyTree ℤ n → Prop
  | 0, .leaf ranges, .leaf _, x, _ => ∀ r ∈ ranges, r.Holds x
  | n + 1, .node ranges L R, .node d l r, x, t =>
      let P := historyPivot (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x)
        t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      (∀ q ∈ ranges, q.Holds x) ∧
        L.ValidAt l (Function.update x d.target P) t.2.1 ∧
        R.ValidAt r (Function.update x d.target P) t.2.2

noncomputable def WordRangeDecoration.formulas {σ : Type*} :
    {n : ℕ} → WordRangeDecoration σ n → WordTransferTemplate σ n →
      (t : FrequencyTree ℤ n) → NonzeroInternalFrequencies n t →
        (σ → HistoryFormula σ) → List (HistoryRange σ)
  | 0, .leaf ranges, .leaf _, _, _, env => ranges.map (fun r => r.toHistory env)
  | n + 1, .node ranges L R, .node d l r, t, ht, env =>
      let next := BranchingWordHistory.updatedFormulas
        (wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ht.1) env
      ranges.map (fun q => q.toHistory env) ++
        (L.formulas l t.2.1 ht.2.1 next ++ R.formulas r t.2.2 ht.2.2 next)

/-- Every intermediate bin, including its endpoints, is precisely a range
of the formula obtained by the original integer reconstruction. -/
theorem WordRangeDecoration.formulas_iff {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (env : σ → HistoryFormula σ) (a : σ → ℤ) (x : σ → ℕ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ))
    (hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t) :
    (∀ r ∈ D.formulas template t ht env, r.Holds a) ↔ D.ValidAt template x t := by
  induction template generalizing env x with
  | leaf word =>
    cases D with
    | leaf ranges =>
      simp only [formulas, ValidAt, List.forall_mem_map]
      exact forall₂_congr fun r _ => r.toHistory_holds env a x henv
  | @node n d l r ihL ihR =>
    cases D with
    | node ranges L R =>
      obtain ⟨P, hp, hvL, hvR⟩ := hv
      have hu := wordTransferUpdatedFormulas_nat d l r x _ _ _ ht.1 P hp env a henv
      simp only [formulas, List.forall_mem_append, List.forall_mem_map, ValidAt, hp.historyPivot_eq]
      apply and_congr (forall₂_congr fun q _ => q.toHistory_holds env a x henv)
      apply and_congr
      · exact ihL L t.2.1 ht.2.1 _ _ hu hvL
      · exact ihR R t.2.2 ht.2.2 _ _ hu hvR

def WordRangeDecoration.count {σ : Type*} : {n : ℕ} → WordRangeDecoration σ n → ℕ
  | 0, .leaf ranges => ranges.length
  | _ + 1, .node ranges L R => ranges.length + L.count + R.count

theorem WordRangeDecoration.formulas_length {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    (D.formulas template t ht env).length = D.count := by
  induction template generalizing env with
  | leaf word => cases D; simp only [formulas, count, List.length_map]
  | node d l r ihL ihR =>
    cases D
    simp only [formulas, count, List.length_append, List.length_map, ihL, ihR]
    omega

end Ostmann

end OAI
