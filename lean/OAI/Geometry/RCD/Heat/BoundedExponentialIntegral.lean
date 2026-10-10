import OAI.Geometry.RCD.Transport.ExponentialTiltVariation

namespace OAI

/-! # Bounded exponential integrals for compact-support kernel scaling

Only a bounded measurable exponent and an integrable weight are needed.
The logarithmic derivative is used for the positive heat-kernel scaling
in the entropic approximation of bounded-support transport plans.
-/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)

theorem bounded_exp_mul_integrable {r g : Y → ℝ} (hr : Integrable r μ)
    (hg : Measurable g) {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) (t : ℝ) :
    Integrable (fun x => Real.exp (t*g x)*r x) μ := by
  have hb : ∀ᵐ x ∂μ, ‖Real.exp (t*g x)‖ ≤ Real.exp (|t| * M) := by
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      t*g x ≤ |t*g x| := le_abs_self _
      _ = |t| * |g x| := abs_mul _ _
      _ ≤ |t| * M := mul_le_mul_of_nonneg_left (hgb x) (abs_nonneg t)
  exact hr.bdd_mul (Real.measurable_exp.comp (measurable_const.mul hg)).aestronglyMeasurable hb

theorem exponential_tilt_integral_hasDerivAt {r g : Y → ℝ} (hr : Integrable r μ)
    (hg : Measurable g) {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ x, Real.exp (s*g x)*r x ∂μ)
      (∫ x, g x*(Real.exp (t*g x)*r x) ∂μ) t := by
  let w := fun x => Real.exp (t*g x)*r x
  have hw : Integrable w μ := bounded_exp_mul_integrable μ hr hg hgb t
  have hz := exponential_tilt_integral_hasDerivAt_zero μ hw hg hgb
  have hshift : HasDerivAt (fun s : ℝ => s-t) 1 t := by
    simpa using (hasDerivAt_id t).sub_const t
  have hh := hz.comp_of_eq t hshift (by simp)
  convert hh using 1
  · funext s
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    dsimp only [Function.comp_def,w]
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    ring
  · simp only [w,mul_one]

theorem log_exponential_tilt_hasDerivAt {r g : Y → ℝ} (hr : Integrable r μ)
    (hg : Measurable g) {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) (t : ℝ)
    (hpos : 0 < ∫ x, Real.exp (t*g x)*r x ∂μ) :
    HasDerivAt (fun s : ℝ => Real.log (∫ x, Real.exp (s*g x)*r x ∂μ))
      ((∫ x, g x*(Real.exp (t*g x)*r x) ∂μ)/(∫ x, Real.exp (t*g x)*r x ∂μ)) t :=
  (exponential_tilt_integral_hasDerivAt μ hr hg hgb t).log hpos.ne'

end RegularPointCoordinates

end

end OAI
