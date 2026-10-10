import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierConstant
import OAI.NumberTheory.CubicMoment.Estimates.GaussianDuality
import OAI.NumberTheory.CubicMoment.Estimates.RieszHeatKernel

namespace OAI

/-! Absolute convergence of the Gaussian representation of the
hyperbolic Fourier kernel. The half-plane is Re(s)>1. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicThetaFourierHeat (v : ℝ) (s w : ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  (t:ℂ)^(s-1)*(Real.exp (-v^2*t)*Real.exp (-t*‖z‖^2):ℝ)*
    (Real.fourierChar (-tracePair z w):ℂ)

lemma cubicThetaFourierHeat_norm (v : ℝ) (s w : ℂ) {t : ℝ}
    (ht : 0 < t) (z : ℂ) :
    ‖cubicThetaFourierHeat v s w t z‖ =
      t^(s.re-1)*Real.exp (-v^2*t)*Real.exp (-t*‖z‖^2) := by
  unfold cubicThetaFourierHeat
  rw [norm_mul, Circle.norm_coe, mul_one, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))]
  simp only [Complex.sub_re, Complex.one_re]
  ring

lemma cubicTheta_gaussian_mass {t : ℝ} (ht : 0 < t) :
    (∫ z : ℂ, Real.exp (-t*‖z‖^2)) = Real.pi/t := by
  simpa only [Complex.finrank_real_complex, Nat.cast_ofNat, div_self (by norm_num : (2:ℝ) ≠ 0),
    Real.rpow_one] using GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) ht

lemma cubicTheta_gaussian_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun z : ℂ => Real.exp (-t*‖z‖^2)) := by
  apply (integrable_trace_gaussian ht).norm.congr
  filter_upwards with z
  have he : -(t:ℂ)*(‖z‖:ℂ)^2 = ((-t*‖z‖^2:ℝ):ℂ) := by push_cast; ring
  rw [he, Complex.norm_exp, Complex.ofReal_re]

lemma cubicThetaFourierHeat_norm_mass (v : ℝ) (s w : ℂ) {t : ℝ}
    (ht : 0 < t) :
    (∫ z : ℂ, ‖cubicThetaFourierHeat v s w t z‖) =
      Real.pi*(t^(s.re-2)*Real.exp (-v^2*t)) := by
  simp_rw [cubicThetaFourierHeat_norm v s w ht]
  rw [integral_const_mul, cubicTheta_gaussian_mass ht]
  have hp : t^(s.re-1)/t = t^(s.re-2) := by
    calc
      _ = t^(s.re-1)/t^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_sub ht]; congr 1; ring
  calc
    _ = Real.pi*(t^(s.re-1)/t*Real.exp (-v^2*t)) := by ring
    _ = _ := by rw [hp]

theorem cubicThetaFourierHeat_integrable {v : ℝ} (hv : 0 < v) {s : ℂ}
    (hs : 1 < s.re) (w : ℂ) :
    Integrable (fun p : ℝ × ℂ => cubicThetaFourierHeat v s w p.1 p.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℂ => cubicThetaFourierHeat v s w p.1 p.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
    apply Measurable.aestronglyMeasurable
    unfold cubicThetaFourierHeat tracePair
    fun_prop
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hmt : AEStronglyMeasurable (cubicThetaFourierHeat v s w t) volume := by
      apply Measurable.aestronglyMeasurable
      unfold cubicThetaFourierHeat tracePair
      fun_prop
    apply ((cubicTheta_gaussian_integrable ht).const_mul
      (t^(s.re-1)*Real.exp (-v^2*t))).mono' hmt
    filter_upwards with z
    rw [cubicThetaFourierHeat_norm v s w ht]
  · have hi := (integrable_laplace_rpow (show 0 < s.re-1 by linarith)
      (sq_pos_of_pos hv)).const_mul Real.pi
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [cubicThetaFourierHeat_norm_mass v s w ht]
    congr 2
    congr 1
    ring

end CubicFirstMoment

end

end OAI
