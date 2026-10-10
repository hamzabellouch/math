import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactRieszPairing

namespace OAI

/-!
# The scalar far Riesz transform

Subtracting the kernel at the localization center gives an integrable far-field
kernel under global upper growth. Quantitative decay bounds yield measurability
and local `L²` control of its scalar integral on the inner ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped NNReal

def scalarFarRieszTransform {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (e a : Ambient d) (R : ℝ) (x : Ambient d) : ℝ :=
  ∫ y in closedExterior a R, inner ℝ e (kernel m x y - kernel m a y) ∂μ

theorem scalar_far_kernel_bound {d : ℕ} (m : ℕ) (e a x y : Ambient d)
    (R : ℝ) (hR : 0 < R) (hx : 2 * dist x a ≤ R) (hy : R ≤ dist a y) :
    |inner ℝ e (kernel m x y - kernel m a y)| ≤
      ((2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) * (‖e‖ * dist x a)) *
        inverseDistancePow (m + 1) a y := by
  let w := affineNormalHeight e a 0
  have hw : LipschitzWith ‖e‖₊ w := affineNormalHeight_lipschitz e a 0
  have hwa : w a = 0 := by simp only [w, affineNormalHeight, sub_self, inner_zero_right]
  have hwx : |w x| ≤ ‖e‖ * dist x a := by
    simpa only [Real.dist_eq, hwa, sub_zero, coe_nnnorm] using! hw.dist_le_mul x a
  have hcancel := cancelled_height_far_bound m w ‖e‖₊ hw a x y R hR hx hy
  simp only [hwa, abs_zero, zero_div, add_zero, coe_nnnorm] at hcancel
  have hk := inverseDistancePow_far_le (m + 1) a x y (hR.trans_le hy) (hx.trans hy)
  have heq : inner ℝ e (kernel m x y - kernel m a y) =
      w x * inverseDistancePow (m + 1) x y -
        w y * (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y) := by
    rw [inner_sub_right, kernel_inner_normal_difference m e w (affineNormalHeight_difference e a 0),
      kernel_inner_normal_difference m e w (affineNormalHeight_difference e a 0), hwa]
    ring
  rw [heq]
  calc
    _ ≤ |w x * inverseDistancePow (m + 1) x y| +
        |w y * (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using!
        abs_sub_le (w x * inverseDistancePow (m + 1) x y) 0
          (w y * (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y))
    _ ≤ (‖e‖ * dist x a) * (2 ^ (m + 1) * inverseDistancePow (m + 1) a y) +
        (‖e‖ * (m + 1 : ℝ) * 2 ^ (m + 2) * dist x a) * inverseDistancePow (m + 1) a y := by
      apply add_le_add _ hcancel
      rw [abs_mul, abs_of_nonneg (inverseDistancePow_nonneg _ _ _)]
      exact mul_le_mul hwx hk (inverseDistancePow_nonneg _ _ _) (by positivity)
    _ = _ := by ring

theorem scalarFarRieszTransform_measurable {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (e a : Ambient d) (R : ℝ) :
    Measurable (scalarFarRieszTransform m μ e a R) := by
  have hm : Measurable (fun q : Ambient d × Ambient d =>
      inner ℝ e (kernel m q.1 q.2 - kernel m a q.2)) := by
    have : IsBoundedSMul ℝ (Ambient d) := NormedSpace.toIsBoundedSMul
    have : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
    have : MeasurableSMul₂ ℝ (Ambient d) := ContinuousSMul.measurableSMul₂
    unfold kernel
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem scalarFarRieszTransform_integrable_and_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (e a x : Ambient d) (R : ℝ) (hR : 0 < R) (hx : 2 * dist x a ≤ R) :
    IntegrableOn (fun y => inner ℝ e (kernel m x y - kernel m a y)) (closedExterior a R) μ ∧
      |scalarFarRieszTransform m μ e a R x| ≤
        ((2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) * (‖e‖ * dist x a)) *
          (2 * (C * 2 ^ m / R)) := by
  let B := (2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) * (‖e‖ * dist x a)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨hk, hbound⟩ := inverseDistancePow_closedExterior_integrable_and_bound m C μ hg a R hR
  have hm : Measurable (fun y => inner ℝ e (kernel m x y - kernel m a y)) := by
    have : IsBoundedSMul ℝ (Ambient d) := NormedSpace.toIsBoundedSMul
    have : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
    have : MeasurableSMul₂ ℝ (Ambient d) := ContinuousSMul.measurableSMul₂
    unfold kernel
    fun_prop
  have hi : IntegrableOn (fun y => inner ℝ e (kernel m x y - kernel m a y)) (closedExterior a R) μ := by
    apply (hk.const_mul B).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with y hy
    simpa only [Real.norm_eq_abs] using! scalar_far_kernel_bound m e a x y R hR hx hy
  refine ⟨hi, ?_⟩
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ y in closedExterior a R, B * inverseDistancePow (m + 1) a y ∂μ := by
      apply integral_mono_ae hi.abs (hk.const_mul B)
      filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with y hy
      exact scalar_far_kernel_bound m e a x y R hR hx hy
    _ = B * ∫ y in closedExterior a R, inverseDistancePow (m + 1) a y ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound hB

theorem scalarFarRieszTransform_memLp_inner_ball {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (e a : Ambient d) (H R : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R) :
    MemLp (scalarFarRieszTransform m μ e a R) 2 (μ.restrict (ball a H)) := by
  let := finiteMeasure_restrict_ball_of_globalGrowth m C μ hg a H hH
  let B := ((2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) * (‖e‖ * H)) *
    (2 * (C * 2 ^ m / R))
  apply MemLp.of_bound (scalarFarRieszTransform_measurable m μ e a R).aestronglyMeasurable B
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  rw [Real.norm_eq_abs]
  have hxH : dist x a ≤ H := hx.le
  have hC := hg.1
  apply (scalarFarRieszTransform_integrable_and_bound m C μ hg e a x R hR (by linarith)).2.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxH (norm_nonneg _)) (by positivity))
    (by positivity)

end

end RieszRectifiability

end OAI
