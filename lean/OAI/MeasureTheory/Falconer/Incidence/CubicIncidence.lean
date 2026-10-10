import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace OAI

/-! # The cubic incidence lower bound needed by three-dimensional slices -/

namespace Falconer
open MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

private theorem cube_rpow (x : ℝ≥0∞) (a : ℝ) : (x^a)^3 = x^(a*3) := by
  rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
  norm_num

theorem cubic_incidence_moment (μ : Measure X) (F : X → ℝ≥0∞) (hF : AEMeasurable F μ) :
    (∫⁻ x, F x ∂μ)^3 ≤ (∫⁻ x, (F x)^3 ∂μ)*(μ Set.univ)^2 := by
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (show (3:ℝ).HolderConjugate (3/2) by norm_num [Real.holderConjugate_iff]) hF
    (aemeasurable_const : AEMeasurable (fun _ : X => (1:ℝ≥0∞)) μ)
  simp only [Pi.mul_apply,mul_one,ENNReal.one_rpow,lintegral_one] at hH
  have hp := pow_le_pow_left' hH 3
  apply hp.trans_eq
  rw [mul_pow]
  rw [cube_rpow,cube_rpow]
  norm_num [ENNReal.rpow_natCast]

end Falconer

end OAI
