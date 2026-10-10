import OAI.Combinatorics.BalancedRyser.Probability.DistinctRoleLaw
import OAI.Combinatorics.BalancedRyser.Selection.LineOccupancyConcentration

namespace OAI

noncomputable section
open Filter Topology
open scoped Classical

namespace Balanced.DistinctRole

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem map_initial_data :
    ((offsetLaw F).filter {M | DistinctConstituents M} distinct_support).map
      (fun M => (initialDeletedLines M, initiallyRetained M)) =
    (offsetLaw F).map (fun M => (initialDeletedLines M, initiallyRetained M)) := by
  let f : (Direction F → F) → Finset (Line F) × Finset (Point F) :=
    fun r => (initialDeletedLines (fun d _ => r d), initiallyRetained (fun d _ => r d))
  exact map_role_one_observable f

theorem initial_event_probability (E : Set (Finset (Line F) × Finset (Point F))) :
    (((offsetLaw F).filter {M | DistinctConstituents M} distinct_support).toOuterMeasure
      {M | (initialDeletedLines M, initiallyRetained M) ∈ E}).toReal =
    offsetEventProbability (F := F)
      {M | (initialDeletedLines M, initiallyRetained M) ∈ E} := by
  have h := congrArg (fun p : PMF (Finset (Line F) × Finset (Point F)) =>
    (p.toOuterMeasure E).toReal) (map_initial_data (F := F))
  simp only [PMF.toOuterMeasure_map_apply] at h
  convert h using 1 <;> congr 2

theorem initial_failure_probability_eq :
    (((offsetLaw F).filter {M | DistinctConstituents M} distinct_support).toOuterMeasure
      {M | ∃ l, l ∉ initialDeletedLines M ∧
        ((linePoints l ∩ initiallyRetained M).card : ℝ) < (Fintype.card F : ℝ) / 5}).toReal =
    offsetEventProbability (F := F)
      {M | ∃ l, l ∉ initialDeletedLines M ∧
        ((linePoints l ∩ initiallyRetained M).card : ℝ) < (Fintype.card F : ℝ) / 5} := by
  exact initial_event_probability
    {z | ∃ l, l ∉ z.1 ∧ ((linePoints l ∩ z.2).card : ℝ) < (Fintype.card F : ℝ) / 5}

theorem initial_failure_probability_le
    (hgap : (Fintype.card F : ℝ) / 20 ≤
      (Fintype.card F : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) ^ Fintype.card F -
        (Fintype.card F : ℝ) / 5) :
    (((offsetLaw F).filter {M | DistinctConstituents M} distinct_support).toOuterMeasure
      {M | ∃ l, l ∉ initialDeletedLines M ∧
        ((linePoints l ∩ initiallyRetained M).card : ℝ) < (Fintype.card F : ℝ) / 5}).toReal ≤
      (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1) *
        (2 * Real.exp (-(Fintype.card F : ℝ) / 3200)) := by
  rw [initial_failure_probability_eq]
  exact LineOccupancy.initial_failure_probability_le hgap

theorem tendsto_initial_failure (F : ℕ → Type*)
    [∀ n, Field (F n)] [∀ n, Fintype (F n)] [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n =>
      (((offsetLaw (F n)).filter {M | DistinctConstituents M} distinct_support).toOuterMeasure
        {M | ∃ l, l ∉ initialDeletedLines M ∧
          ((linePoints l ∩ initiallyRetained M).card : ℝ) < (Fintype.card (F n) : ℝ) / 5}).toReal)
      atTop (𝓝 0) := by
  simpa only [initial_failure_probability_eq] using LineOccupancy.tendsto_initial_failure F hq

end Balanced.DistinctRole

end

end OAI
