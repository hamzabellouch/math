import OAI.Geometry.RCD.Transport.LengthBinIntegral
import OAI.Geometry.RCD.Transport.RenyiSubmeasureBound

namespace OAI

/-! # Two independent endpoint weights on a finite length partition -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem weighted_length_bin_lintegral (π : Measure C(Time,X))
    {D ε : ℝ} (hε : 0<ε) (hD : ∀ᵐ γ ∂π, dist (γ 0) (γ 1)≤D)
    (w : ℝ → ℝ≥0∞) (g : C(Time,X) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ γ, w (upperLength ε (dist (γ 0) (γ 1)))*g γ ∂π)=
      ∑ i∈Finset.range (⌊D/ε⌋₊+1), w (((i:ℝ)+1)*ε)*
        ∫⁻ γ, g γ ∂π.restrict {γ | dist (γ 0) (γ 1)∈lengthBin ε i} := by
  let κ := fun i => π.restrict {γ | dist (γ 0) (γ 1)∈lengthBin ε i}
  have hsum := bounded_length_uniform_partition π hε hD
  calc
    _ = ∫⁻ γ, w (upperLength ε (dist (γ 0) (γ 1)))*g γ
        ∂∑ i∈Finset.range (⌊D/ε⌋₊+1), κ i := by rw [hsum]
    _ = ∑ i∈Finset.range (⌊D/ε⌋₊+1),
        ∫⁻ γ, w (upperLength ε (dist (γ 0) (γ 1)))*g γ ∂κ i :=
      lintegral_finsetSum_measure _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [←lintegral_const_mul _ hg]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem ((lengthBin_measurable ε i).preimage
        ((measurable_path_eval 0).dist (measurable_path_eval 1)))] with γ hγ
      rw [upperLength,floor_eq_of_mem_lengthBin hε hγ]

theorem weighted_chord_bin_entropy (μ : Measure X) [SigmaFinite μ]
    {N : ℝ} (hN : 1<N) (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (h0 : π.map (fun γ => γ 0) ≪ μ) (h1 : π.map (fun γ => γ 1) ≪ μ)
    (w₀ w₁ : ℝ → ℝ≥0∞) {D ε : ℝ} (hε : 0<ε)
    (hD : ∀ᵐ γ ∂π, dist (γ 0) (γ 1)≤D) :
    (∫⁻ γ, w₀ (upperLength ε (dist (γ 0) (γ 1)))*
      ((π.map (fun γ => γ 0)).rnDeriv μ (γ 0))^(-(1/N))+
      w₁ (upperLength ε (dist (γ 0) (γ 1)))*
      ((π.map (fun γ => γ 1)).rnDeriv μ (γ 1))^(-(1/N)) ∂π) ≤
    ∑ i∈Finset.range (⌊D/ε⌋₊+1),
      (w₀ (((i:ℝ)+1)*ε)*renyiIntegral μ ((π.restrict {γ | dist (γ 0) (γ 1)∈lengthBin ε i}).map (fun γ => γ 0)) N+
      w₁ (((i:ℝ)+1)*ε)*renyiIntegral μ ((π.restrict {γ | dist (γ 0) (γ 1)∈lengthBin ε i}).map (fun γ => γ 1)) N) := by
  let κ := fun i => π.restrict {γ | dist (γ 0) (γ 1)∈lengthBin ε i}
  let g := fun (t : Time) (γ : C(Time,X)) => ((π.map (fun γ => γ t)).rnDeriv μ (γ t))^(-(1/N))
  have hg (t : Time) : Measurable (g t) :=
    (((π.map (fun γ => γ t)).measurable_rnDeriv μ).comp (measurable_path_eval t)).pow_const _
  have hw (w : ℝ → ℝ≥0∞) : Measurable (fun γ : C(Time,X) => w (upperLength ε (dist (γ 0) (γ 1)))) :=
    (measurable_of_countable (fun i : ℕ => w (((i:ℝ)+1)*ε))).comp
      (((measurable_path_eval 0).dist (measurable_path_eval 1)).div_const ε).nat_floor
  have hi (i) (t : Time) (ht : π.map (fun γ => γ t) ≪ μ) :
      (∫⁻ γ, g t γ ∂κ i)≤renyiIntegral μ ((κ i).map (fun γ => γ t)) N := by
    rw [←lintegral_map (((π.map (fun γ => γ t)).measurable_rnDeriv μ).pow_const _)
      (measurable_path_eval t)]
    exact inverse_density_lintegral_le_renyi μ _ _ ht
      (Measure.map_mono Measure.restrict_le_self (measurable_path_eval t)) hN
  change (∫⁻ γ, w₀ (upperLength ε (dist (γ 0) (γ 1)))*g 0 γ+
    w₁ (upperLength ε (dist (γ 0) (γ 1)))*g 1 γ ∂π)≤_
  have hm0 : Measurable (fun γ => w₀ (upperLength ε (dist (γ 0) (γ 1)))*g 0 γ) :=
    (hw w₀).mul (hg 0)
  rw [lintegral_add_left hm0,weighted_length_bin_lintegral π hε hD w₀ _ (hg 0),
    weighted_length_bin_lintegral π hε hD w₁ _ (hg 1),←Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => add_le_add
    (mul_le_mul' le_rfl (hi i 0 h0)) (mul_le_mul' le_rfl (hi i 1 h1)))

end RegularPointCoordinates

end

end OAI
