import OAI.Geometry.RCD.Sobolev.CompactBochnerTest

namespace OAI

/-! # Cancellation of the constant local Laplacian in the Bochner formula -/

open Set Filter MeasureTheory
open scoped NNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem constant_source_cancellation (u : SobolevSpace μ hQ) (d : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ hQ u d) {Ω : Set X} (hΩ : MeasurableSet Ω)
    (c : ℝ) (hc : d =ᵐ[μ.restrict Ω] fun _ => c)
    (w : SobolevSpace μ hQ) (v : X → ℝ)
    (hw : SobolevSpace.toLp μ hQ w =ᵐ[μ] v) (hs : tsupport v ⊆ Ω) :
    (∫ x, v x * (d x) ^ 2 ∂μ) + weightedGamma μ hQ d u w = 0 := by
  have hc' := (ae_restrict_iff' hΩ).mp hc
  have hv0 (x : X) (hx : x ∉ Ω) : v x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm => hx (hs hm))
  have hi : inner ℝ d (SobolevSpace.toLp μ hQ w) = c * ∫ x, v x ∂μ := by
    rw [L2.inner_def, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hw, hc'] with x hx hcx
    change SobolevSpace.toLp μ hQ w x * d x = c * v x
    rw [hx]
    by_cases hmem : x ∈ Ω
    · rw [hcx hmem, mul_comm]
    · rw [hv0 x hmem, zero_mul, mul_zero]
  have hsq : (∫ x, v x * (d x) ^ 2 ∂μ) = c ^ 2 * ∫ x, v x ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hc'] with x hx
    by_cases hmem : x ∈ Ω
    · rw [hx hmem, mul_comm]
    · rw [hv0 x hmem, zero_mul, mul_zero]
  have hm : weightedGamma μ hQ d u w = c * energyForm μ hQ u w := by
    rw [← integral_localGamma_eq_energyForm, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hc', hw, localGamma_comm μ hQ u w,
      localGamma_zero_on_level μ hQ w u 0] with x hx hwx hcomm hzero
    change d x * localGamma μ hQ u w x = c * localGamma μ hQ u w x
    by_cases hmem : x ∈ Ω
    · rw [hx hmem]
    · rw [hcomm, hzero (hwx.trans (hv0 x hmem)), mul_zero, mul_zero]
  rw [hsq, hm, hd w, hi]
  ring

end RegularPointCoordinates

end OAI
