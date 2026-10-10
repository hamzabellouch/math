import OAI.Geometry.RCD.Transport.RenyiLocalization

namespace OAI

/-! # The inverse-density expression for the Rényi integral -/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem renyiIntegral_eq_inverse_density (μ ν : Measure X) [SigmaFinite μ]
    [IsFiniteMeasure ν] (hac : ν ≪ μ) {N : ℝ} (hN : 1 < N) :
    renyiIntegral μ ν N = ∫⁻ x, (ν.rnDeriv μ x)^(-(1/N)) ∂ν := by
  have hq : 0 < 1-1/N := sub_pos.mpr ((div_lt_one (by linarith : 0<N)).mpr hN)
  rw [←lintegral_rnDeriv_mul hac ((ν.measurable_rnDeriv μ).pow_const _).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [Measure.rnDeriv_lt_top ν μ] with x hx
  by_cases h0 : ν.rnDeriv μ x=0
  · rw [h0,zero_mul,ENNReal.zero_rpow_of_pos hq]
  rw [show 1-1/N = 1+(-(1/N)) by ring,ENNReal.rpow_add _ _ h0 hx.ne]
  simp

end RegularPointCoordinates

end

end OAI
