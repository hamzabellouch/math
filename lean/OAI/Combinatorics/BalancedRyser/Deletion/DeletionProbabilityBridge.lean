import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Deletion.Deletion

namespace OAI

open MeasureTheory

namespace Balanced
open scoped _root_.Balanced

theorem pmf_real_event_eq_sum {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (Q : PMF α) (E : α → Prop) [DecidablePred E] :
    Q.toMeasure.real {x | E x} = ∑ x, if E x then (Q x).toReal else 0 := by
  classical
  rw [measureReal_def, Q.toMeasure_apply_fintype]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro x hx
    by_cases h : E x <;> simp [h]
  · intro x hx
    by_cases h : E x
    · simpa [Set.indicator_apply, h] using Q.apply_ne_top x
    · simp [h]

theorem deletionEventProbability_eq_toMeasure
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k : ℕ}
    [MeasurableSpace (DeletionSet F k)] [MeasurableSingletonClass (DeletionSet F k)]
    (Q : PMF (DeletionSet F k)) (E : DeletionSet F k → Prop) :
    deletionEventProbability Q E = Q.toMeasure.real {D | E D} := by
  classical
  exact (pmf_real_event_eq_sum Q E).symm

theorem deletionEventProbability_toPMF
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k : ℕ}
    [MeasurableSpace (DeletionSet F k)] [MeasurableSingletonClass (DeletionSet F k)]
    (μ : Measure (DeletionSet F k)) [IsProbabilityMeasure μ]
    (E : DeletionSet F k → Prop) :
    deletionEventProbability μ.toPMF E = μ.real {D | E D} := by
  rw [deletionEventProbability_eq_toMeasure, Measure.toPMF_toMeasure]

theorem deletionDominated_toPMF
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k : ℕ}
    [MeasurableSpace (DeletionSet F k)] [MeasurableSingletonClass (DeletionSet F k)]
    (μ : Measure (DeletionSet F k)) [IsProbabilityMeasure μ] (K : ℝ)
    (h : ∀ D, μ.real {D} ≤ Real.exp (K * (Fintype.card F : ℝ)) *
      uniformDeletionMass (F := F) k) :
    DeletionDominated k K μ.toPMF := by
  intro D
  simpa only [Measure.toPMF_apply, measureReal_def] using h D

end Balanced

end OAI
