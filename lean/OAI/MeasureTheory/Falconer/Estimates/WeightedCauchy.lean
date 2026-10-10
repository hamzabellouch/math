import OAI.MeasureTheory.Falconer.Angular.SharedAngular
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! # The L1 cost of the spatial Fourier separation

The coefficient is integrated before estimating the shell energy. Its
squared cost is controlled by one L1 factor and a positive weighted energy.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem norm_integral_weighted_sq_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (c F : X → ℂ) (hcm : Measurable c) (hc : Integrable c μ)
    (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, ‖F x‖ ≤ B) :
    ‖∫ x, c x*F x ∂μ‖^2 ≤
      (∫ x, ‖c x‖ ∂μ) * ∫ x, ‖c x‖*‖F x‖^2 ∂μ := by
  let τ := μ.withDensity (fun x => ENNReal.ofReal ‖c x‖)
  let : IsFiniteMeasure τ := isFiniteMeasure_withDensity_ofReal hc.norm.2
  have hchange (g : X → ℝ) : (∫ x, g x ∂τ) = ∫ x, ‖c x‖*g x ∂μ := by
    change (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal ‖c x‖)) = _
    rw [integral_withDensity_eq_integral_toReal_smul hcm.norm.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (norm_nonneg _),smul_eq_mul]
  have hsq : Integrable (fun x => ‖F x‖^2) τ := by
    apply Integrable.of_bound (hF.norm.pow_const 2).aestronglyMeasurable (B^2)
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) hB).mpr (hb x)
  have hn : Integrable (fun x => ‖F x‖) τ := by
    apply Integrable.of_bound hF.norm.aestronglyMeasurable B
    filter_upwards with x
    simpa only [norm_norm] using hb x
  have hcs := real_integral_product_sq_le τ (fun x => ‖F x‖) (fun _ => (1:ℝ))
    hsq (by simpa only [one_pow] using (integrable_const (1:ℝ) (μ := τ)))
    (by simpa only [mul_one] using hn)
  simp only [mul_one,one_pow,hchange] at hcs
  have hprod : Integrable (fun x => ‖c x‖*‖F x‖) μ := by
    apply (hc.norm.mul_const B).mono' (hcm.norm.mul hF.norm).aestronglyMeasurable
    filter_upwards with x
    change ‖‖c x‖*‖F x‖‖ ≤ ‖c x‖*B
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)
  have hnorm : ‖∫ x, c x*F x ∂μ‖ ≤ ∫ x, ‖c x‖*‖F x‖ ∂μ := by
    apply norm_integral_le_of_norm_le hprod
    filter_upwards with x
    rw [norm_mul]
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans (by
    simpa only [mul_one,mul_comm] using hcs)

end Falconer

end OAI
