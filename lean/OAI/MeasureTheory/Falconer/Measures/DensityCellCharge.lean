import OAI.MeasureTheory.Falconer.Measures.FiberDensityPruning

namespace OAI

/-! # Charging the full masses of hit children before the final density deletion -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X ι : Type*} [MeasurableSpace X]

theorem density_hit_children_charge (μ : Measure X) (S P T : Set X)
    (hS : MeasurableSet S) (Q : ι → Set X) (I : Finset ι)
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hdisj : (I : Set ι).PairwiseDisjoint Q)
    {θ F : ℝ≥0∞} (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hdensity : ∀ i ∈ I, θ*μ (Q i) ≤ μ (Q i ∩ S))
    (hlocal : ∀ i ∈ I, Q i ∩ S ⊆ P ∩ T)
    (htest : μ (P ∩ T) ≤ F*μ P) :
    (∑ i ∈ I, μ (Q i)) ≤ (θ⁻¹*F)*μ P := by
  have hi : (I : Set ι).PairwiseDisjoint (fun i => Q i ∩ S) := by
    intro i hi j hj hij
    exact (hdisj hi hj hij).mono inter_subset_left inter_subset_left
  have hm : θ*(∑ i ∈ I, μ (Q i)) ≤ F*μ P := by
    calc
      _ = ∑ i ∈ I, θ*μ (Q i) := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ I, μ (Q i ∩ S) := Finset.sum_le_sum hdensity
      _ = μ (⋃ i ∈ I, Q i ∩ S) := (measure_biUnion_finset hi (fun i hi => (hQ i hi).inter hS)).symm
      _ ≤ μ (P ∩ T) := measure_mono (iUnion₂_subset hlocal)
      _ ≤ _ := htest
  calc
    _ = θ⁻¹*(θ*(∑ i ∈ I, μ (Q i))) := by
      rw [← mul_assoc,ENNReal.inv_mul_cancel hθ.ne' hθtop,one_mul]
    _ ≤ θ⁻¹*(F*μ P) := mul_le_mul' le_rfl hm
    _ = _ := (mul_assoc _ _ _).symm

end Falconer

end OAI
