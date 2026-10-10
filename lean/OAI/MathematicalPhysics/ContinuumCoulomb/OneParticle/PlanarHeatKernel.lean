import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarForcing
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

namespace OAI

/-! The actual normalized two-dimensional Gaussian heat kernel and its
convolution with the paper's explicit forcing. These prepare the positive
resolvent mode, rather than assuming the manufactured well exists. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def planarHeatKernel (t : ℝ) (r : PlanarPosition) : ℝ :=
  (4 * Real.pi * t)⁻¹ * Real.exp (-‖r‖ ^ 2 / (4 * t))

theorem planarHeatKernel_positive {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    0 < planarHeatKernel t r := by
  exact mul_pos (inv_pos.mpr (by positivity)) (Real.exp_pos _)

theorem planarHeatKernel_continuous (t : ℝ) : Continuous (planarHeatKernel t) := by
  unfold planarHeatKernel
  fun_prop

theorem planar_gaussian_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun r : PlanarPosition => Real.exp (-b * ‖r‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := PlanarPosition) (b := (b : ℂ)) (by simpa using hb) 0 0
  have hc : Integrable (fun r : PlanarPosition => Complex.exp ((-b * ‖r‖ ^ 2 : ℝ) : ℂ)) := by
    simpa only [zero_mul, add_zero, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_pow] using h
  simpa only [Complex.norm_exp, Complex.ofReal_re] using hc.norm

theorem planarHeatKernel_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (planarHeatKernel t) := by
  unfold planarHeatKernel
  have h := (planar_gaussian_integrable (b := (4 * t)⁻¹) (by positivity)).const_mul
    ((4 * Real.pi * t)⁻¹)
  convert h using 1
  funext r
  congr 2
  ring

theorem planarHeatKernel_integral {t : ℝ} (ht : 0 < t) :
    (∫ r, planarHeatKernel t r) = 1 := by
  have heq : (fun r : PlanarPosition => Real.exp (-‖r‖ ^ 2 / (4 * t))) =
      (fun r : PlanarPosition => Real.exp (-(4 * t)⁻¹ * ‖r‖ ^ 2)) := by
    funext r
    congr 1
    ring
  unfold planarHeatKernel
  rw [integral_const_mul, heq,
    GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity : 0 < (4 * t)⁻¹)]
  norm_num [finrank_euclideanSpace_fin]
  field_simp [ht.ne', Real.pi_ne_zero]

def planarHeatAverage (t : ℝ) (r : PlanarPosition) : ℝ :=
  ∫ b, planarHeatKernel t b * planarForcing (r - b)

theorem planarHeatAverage_integrand_integrable {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    Integrable (fun b => planarHeatKernel t b * planarForcing (r - b)) := by
  apply (planarHeatKernel_integrable ht).mul_bdd
    ((planarForcing_C7.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun b => by
    change ‖planarForcing (r - b)‖ ≤ (1 : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (planarForcing_nonnegative _)]
    exact planarForcing_le_one _)

theorem planarHeatAverage_positive {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    0 < planarHeatAverage t r := by
  apply integral_pos_of_integrable_nonneg_nonzero
    ((planarHeatKernel_continuous t).mul
      (planarForcing_C7.continuous.comp (continuous_const.sub continuous_id)))
    (planarHeatAverage_integrand_integrable ht r)
    (fun b => mul_nonneg (planarHeatKernel_positive ht b).le (planarForcing_nonnegative _))
  change planarHeatKernel t r * planarForcing (r - r) ≠ 0
  simpa only [sub_self, planarForcing_zero, mul_one] using (planarHeatKernel_positive ht r).ne'

theorem planarHeatAverage_le_one {t : ℝ} (ht : 0 < t) (r : PlanarPosition) :
    planarHeatAverage t r ≤ 1 := by
  rw [← planarHeatKernel_integral ht]
  apply integral_mono (planarHeatAverage_integrand_integrable ht r) (planarHeatKernel_integrable ht)
  intro b
  exact mul_le_of_le_one_right (planarHeatKernel_positive ht b).le (planarForcing_le_one _)

end ContinuumCoulomb

end

end OAI
