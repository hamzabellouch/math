import OAI.Geometry.RCD.Transport.MidpointLengthApproximation

namespace OAI

/-! # Exact integration of a constant distortion coefficient on each bin -/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates

theorem floor_eq_of_mem_lengthBin {ε d : ℝ} {i : ℕ} (hε : 0<ε)
    (hd : d∈lengthBin ε i) : ⌊d/ε⌋₊=i := by
  have hd0 : 0≤d := (mul_nonneg (Nat.cast_nonneg _) hε.le).trans hd.1
  apply (Nat.floor_eq_iff (div_nonneg hd0 hε.le)).mpr
  exact ⟨(le_div_iff₀ hε).mpr hd.1,(div_lt_iff₀ hε).mpr hd.2⟩

theorem measurable_midpoint_upperLength (K N ε : ℝ) :
    Measurable (fun d : ℝ => sigma K N (1/2) (upperLength ε d/2)) := by
  exact (measurable_of_countable (fun i : ℕ =>
    sigma K N (1/2) ((((i:ℝ)+1)*ε)/2))).comp (measurable_id.div_const ε).nat_floor

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem midpoint_bin_lintegral (K N : ℝ) (π : Measure C(Time,X))
    {D ε : ℝ} (hε : 0<ε) (hD : ∀ᵐ γ ∂π, dist (γ 0) (γ 1)≤D)
    (g : C(Time,X) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ γ, sigma K N (1/2) (upperLength ε (dist (γ 0) (γ 1))/2)*g γ ∂π)=
      ∑ i∈Finset.range (⌊D/ε⌋₊+1), sigma K N (1/2) ((((i:ℝ)+1)*ε)/2)*
        ∫⁻ γ, g γ ∂π.restrict {γ | dist (γ 0) (γ 1)∈lengthBin ε i} := by
  let κ := fun i => π.restrict {γ | dist (γ 0) (γ 1)∈lengthBin ε i}
  have hsum := bounded_length_uniform_partition π hε hD
  calc
    _ = ∫⁻ γ, sigma K N (1/2) (upperLength ε (dist (γ 0) (γ 1))/2)*g γ
        ∂∑ i∈Finset.range (⌊D/ε⌋₊+1), κ i := by rw [hsum]
    _ = ∑ i∈Finset.range (⌊D/ε⌋₊+1),
        ∫⁻ γ, sigma K N (1/2) (upperLength ε (dist (γ 0) (γ 1))/2)*g γ ∂κ i :=
      lintegral_finsetSum_measure _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [←lintegral_const_mul _ hg]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem ((lengthBin_measurable ε i).preimage
        ((measurable_path_eval 0).dist (measurable_path_eval 1)))] with γ hγ
      rw [upperLength,floor_eq_of_mem_lengthBin hε hγ]

end RegularPointCoordinates

end

end OAI
