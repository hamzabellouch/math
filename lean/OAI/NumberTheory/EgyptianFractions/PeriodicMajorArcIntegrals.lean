import OAI.NumberTheory.EgyptianFractions.PeriodicMajorArcs
import OAI.NumberTheory.EgyptianFractions.MinorArcMeasure

namespace OAI
noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace Problem337.MinorArc

/-- Exact disjoint finite-sum decomposition on any measurable integration set.
The normalized zero center retains both pieces crossing the unit endpoints. -/
theorem integral_majorArcs_inter_eq_sum {Q N : ℕ} (hQN : 2 * Q < N)
    {E : Set ℝ} (hE : MeasurableSet E) (f : ℝ → ℂ)
    (hf : IntegrableOn f (majorArcs Q N ∩ E)) :
    (∫ x in majorArcs Q N ∩ E, f x) =
      ∑ r ∈ normalizedCenters Q, ∫ x in periodicArc N r ∩ E, f x := by
  have heq : majorArcs Q N ∩ E =
      ⋃ r ∈ normalizedCenters Q, periodicArc N r ∩ E := by
    rw [majorArcs_eq_iUnion_periodic]
    ext x
    simp only [mem_inter_iff, mem_iUnion]
    aesop
  rw [heq]
  apply integral_biUnion_finset
  · intro r hr
    exact (measurableSet_periodicArc N r).inter hE
  · intro r hr s hs hrs
    exact (pairwiseDisjoint_periodicArcs hQN hr hs hrs).mono
      inter_subset_left inter_subset_left
  · intro r hr
    apply hf.mono_set
    intro x hx
    refine ⟨?_, hx.2⟩
    rw [majorArcs_eq_iUnion_periodic]
    exact mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨hr, hx.1⟩⟩

/-- The full integral separates into the exact finite major-arc sum and the
minor-arc remainder; no endpoint contribution is omitted. -/
theorem integral_eq_majorArc_sum_add_minor {Q N : ℕ} (hQN : 2 * Q < N)
    {E : Set ℝ} (hE : MeasurableSet E) (f : ℝ → ℂ)
    (hf : IntegrableOn f E) :
    (∫ x in E, f x) =
      (∑ r ∈ normalizedCenters Q, ∫ x in periodicArc N r ∩ E, f x) +
        ∫ x in E \ majorArcs Q N, f x := by
  have hsplit := integral_inter_add_sdiff (measurableSet_majorArcs Q N) hf
  rw [inter_comm E (majorArcs Q N)] at hsplit
  rw [integral_majorArcs_inter_eq_sum hQN hE f (hf.mono_set inter_subset_right)]
    at hsplit
  exact hsplit.symm

/-- Continuous circle-method integrands automatically meet the integrability
hypothesis on the compact unit interval. -/
theorem integral_unit_eq_majorArc_sum_add_minor {Q N : ℕ} (hQN : 2 * Q < N)
    (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ x in Icc (0 : ℝ) 1, f x) =
      (∑ r ∈ normalizedCenters Q,
        ∫ x in periodicArc N r ∩ Icc (0 : ℝ) 1, f x) +
        ∫ x in Icc (0 : ℝ) 1 \ majorArcs Q N, f x := by
  exact integral_eq_majorArc_sum_add_minor hQN measurableSet_Icc f
    hf.continuousOn.integrableOn_Icc

end Problem337.MinorArc

end

end OAI
