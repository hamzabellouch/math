import OAI.NumberTheory.TwoPoint.Circuits.CircuitDecisionRestriction
import OAI.NumberTheory.TwoPoint.Circuits.CircuitSwitchingLemma

namespace OAI

/-! Switching a gate whose inputs already have shallow decision trees.
The number of clauses is irrelevant to the switching estimate. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def decisionTreeDisjunction {n k : ℕ} (T : Fin k → BooleanDecisionTree n) :
    List (CubeTerm n) :=
  (univ : Finset (Fin k)).toList.flatMap (fun i => (T i).toDNF)

theorem decisionTreeDisjunction_eval {n k : ℕ} (T : Fin k → BooleanDecisionTree n)
    (x : BooleanCube n) :
    dnfEval (decisionTreeDisjunction T) x = decide (∃ i, (T i).eval x = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [dnfEval_eq_true, decisionTreeDisjunction, List.mem_flatMap,
    Finset.mem_toList, mem_univ, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨C, ⟨i, hC⟩, he⟩
    exact ⟨i, (T i).toDNF_eval x ▸ (dnfEval_eq_true _ _).mpr ⟨C, hC, he⟩⟩
  · rintro ⟨i, hi⟩
    have hh : dnfEval (T i).toDNF x = true := by rwa [(T i).toDNF_eval]
    obtain ⟨C, hC, he⟩ := (dnfEval_eq_true _ _).mp hh
    exact ⟨C, ⟨i, hC⟩, he⟩

theorem decisionTreeDisjunction_width {n k r : ℕ} (T : Fin k → BooleanDecisionTree n)
    (hT : ∀ i, (T i).depth ≤ r) :
    ∀ C ∈ decisionTreeDisjunction T, C.support.card ≤ r := by
  intro C hC
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hC
  exact ((T i).toDNF_width C hi).trans (hT i)

theorem disjunction_restriction_switching {n k r : ℕ} (f : Fin k → BooleanCube n → Bool)
    (hf : ∀ i, HasSmallDecisionTree (f i) r)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1)
    (hq : ((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p)) ≤ 1 / 2) :
    (restrictionLaw n p hp hp1.le).probability (fun ρ =>
      ¬ HasSmallDecisionTree (fun x => decide (∃ i, f i (ρ.apply x) = true)) r) ≤
      2 * (((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p))) ^ (r + 1) := by
  choose T hT he using hf
  have hF := decisionTreeDisjunction_width T hT
  have hh := dnf_restriction_has_shallow_tree (decisionTreeDisjunction T) hF p hp hp1 hq r
  apply (FiniteLaw.probability_mono _ ?_).trans hh
  intro ρ hρ hgood
  apply hρ
  obtain ⟨S, hS, hs⟩ := hgood
  refine ⟨S, hS, ?_⟩
  intro x
  rw [hs, decisionTreeDisjunction_eval]
  simp only [he]

theorem conjunction_restriction_switching {n k r : ℕ} (f : Fin k → BooleanCube n → Bool)
    (hf : ∀ i, HasSmallDecisionTree (f i) r)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1)
    (hq : ((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p)) ≤ 1 / 2) :
    (restrictionLaw n p hp hp1.le).probability (fun ρ =>
      ¬ HasSmallDecisionTree (fun x => decide (∀ i, f i (ρ.apply x) = true)) r) ≤
      2 * (((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p))) ^ (r + 1) := by
  have hh := disjunction_restriction_switching (fun i x => Bool.not (f i x))
    (fun i => (hf i).negate) p hp hp1 hq
  apply (FiniteLaw.probability_mono _ ?_).trans hh
  intro ρ hρ hgood
  apply hρ
  have heq : (fun x => Bool.not (decide (∃ i, Bool.not (f i (ρ.apply x)) = true))) =
      (fun x => decide (∀ i, f i (ρ.apply x) = true)) := by
    funext x
    by_cases hall : ∀ i, f i (ρ.apply x) = true
    · simp [hall]
    · obtain ⟨i, hi⟩ := not_forall.mp hall
      have hn : ∃ i, Bool.not (f i (ρ.apply x)) = true := by
        refine ⟨i, ?_⟩
        cases h : f i (ρ.apply x) <;> simp_all
      simp only [hn, decide_true, Bool.not_true, hall, decide_false]
  have hneg := hgood.negate
  exact Eq.mp (congrArg (fun f => HasSmallDecisionTree f r) heq) hneg

end TwoPointCorrelations

end OAI
