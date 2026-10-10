import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! # Recombining local pair deletions with their original source-cell masses -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem conditional_pair_mass_reconstruct (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [SFinite ν] (Q : Set X) (hQ : μ Q ≠ 0) (E : Set (X × Y)) :
    μ Q*((ProbabilityTheory.cond μ Q).prod ν) E = ((μ.restrict Q).prod ν) E := by
  rw [ProbabilityTheory.cond,Measure.prod_smul_left,Measure.smul_apply,smul_eq_mul,
    ← mul_assoc,ENNReal.mul_inv_cancel hQ (measure_ne_top μ Q),one_mul]

theorem cellwise_pair_deletion_bound (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (I : Finset ι) (Q : ι → Set X) (E : ι → Set (X × Y))
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hE : ∀ i ∈ I, MeasurableSet (E i))
    (hdisj : (I : Set ι).PairwiseDisjoint Q) (t : ℝ≥0∞)
    (hlocal : ∀ i ∈ I, ((μ.restrict (Q i)).prod ν) (E i) ≤ t*μ (Q i)) :
    (μ.prod ν) (⋃ i ∈ I, E i ∩ (Q i ×ˢ univ)) ≤ t*μ univ := by
  calc
    _ ≤ ∑ i ∈ I, (μ.prod ν) (E i ∩ (Q i ×ˢ univ)) := measure_biUnion_finset_le _ _
    _ = ∑ i ∈ I, ((μ.restrict (Q i)).prod ν) (E i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Measure.restrict_prod_eq_prod_univ,Measure.restrict_apply (hE i hi)]
    _ ≤ ∑ i ∈ I, t*μ (Q i) := Finset.sum_le_sum hlocal
    _ = t*(∑ i ∈ I, μ (Q i)) := (Finset.mul_sum _ _ _).symm
    _ = t*μ (⋃ i ∈ I, Q i) := by rw [measure_biUnion_finset hdisj hQ]
    _ ≤ _ := mul_le_mul' le_rfl (measure_mono (subset_univ _))

theorem conditional_cellwise_pair_deletion (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [SFinite ν] (I : Finset ι) (Q : ι → Set X) (E : ι → Set (X × Y))
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hE : ∀ i ∈ I, MeasurableSet (E i))
    (hpos : ∀ i ∈ I, μ (Q i) ≠ 0) (hdisj : (I : Set ι).PairwiseDisjoint Q) (t : ℝ≥0∞)
    (hlocal : ∀ i ∈ I, ((ProbabilityTheory.cond μ (Q i)).prod ν) (E i) ≤ t) :
    (μ.prod ν) (⋃ i ∈ I, E i ∩ (Q i ×ˢ univ)) ≤ t*μ univ := by
  apply cellwise_pair_deletion_bound μ ν I Q E hQ hE hdisj t
  intro i hi
  rw [← conditional_pair_mass_reconstruct μ ν (Q i) (hpos i hi) (E i),mul_comm t]
  exact mul_le_mul' le_rfl (hlocal i hi)

end Falconer

end OAI
