import OAI.NumberTheory.CubicMoment.Estimates.RieszIntegrability
import OAI.NumberTheory.CubicMoment.Estimates.RieszHeatKernel

namespace OAI

/-! Absolute convergence for the Gaussian representation of the Riesz pairing. -/

noncomputable section
open scoped SchwartzMap
open MeasureTheory Set
namespace CubicFirstMoment

private lemma ae_complex_ne_zero : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by
  rw [ae_iff]
  simp

def rieszGaussianWeight (a : ℝ) (z : ℂ) (t : ℝ) : ℝ :=
  t^(a-1)*Real.exp (-‖z‖^2*t)

lemma rieszGaussianWeight_integral {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z ≠ 0) :
    (∫ t in Ioi (0:ℝ), rieszGaussianWeight a z t) = Real.Gamma a*‖z‖^(-2*a) := by
  simp only [rieszGaussianWeight]
  rw [laplace_rpow ha (sq_pos_of_pos (norm_pos_iff.mpr hz))]
  congr 1
  rw [← Real.rpow_natCast ‖z‖ 2,← Real.rpow_mul (_root_.norm_nonneg z)]
  congr 1
  ring

lemma rieszGaussianWeight_nonneg (a : ℝ) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    0 ≤ rieszGaussianWeight a z t :=
  mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _)

/-- Tonelli's integrability criterion makes the subsequent interchange
of the Gaussian and spatial integrals legitimate. -/
theorem integrable_riesz_gaussian_product (F : 𝓢(ℂ,ℂ)) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) :
    Integrable (fun p : ℂ × ℝ => (rieszGaussianWeight a p.1 p.2 : ℂ)*F p.1)
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hm : AEStronglyMeasurable
      (fun p : ℂ × ℝ => (rieszGaussianWeight a p.1 p.2 : ℂ)*F p.1)
      (volume.prod (volume.restrict (Ioi 0))) := by
    apply Measurable.aestronglyMeasurable
    unfold rieszGaussianWeight
    fun_prop
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_complex_ne_zero] with z hz
    exact (integrable_laplace_rpow ha (sq_pos_of_pos (norm_pos_iff.mpr hz))).ofReal.mul_const (F z)
  · have hw : Integrable (fun z : ℂ => Real.Gamma a*(‖z‖^(-2*a)*‖F z‖)) := by
      have h := (schwartz_riesz_integrable F (mul_pos (by norm_num : (0:ℝ) < 2) ha)
        (by linarith : 2*a < 2)).norm.const_mul (Real.Gamma a)
      convert h using 1
      funext z
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg (_root_.norm_nonneg z) _)]
      simp only [neg_mul]
    apply hw.congr
    filter_upwards [ae_complex_ne_zero] with z hz
    calc
      _ = (∫ t in Ioi (0:ℝ), rieszGaussianWeight a z t)*‖F z‖ := by
        rw [rieszGaussianWeight_integral ha hz]
        ring
      _ = ∫ t in Ioi (0:ℝ), rieszGaussianWeight a z t*‖F z‖ := (integral_mul_const _ _).symm
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (rieszGaussianWeight_nonneg a z ht)]

/-- Fubini applied to the absolutely integrable Gaussian representation. -/
theorem riesz_integral_eq_gaussian_integral (F : 𝓢(ℂ,ℂ)) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) :
    (Real.Gamma a:ℂ)*(∫ z : ℂ, ((‖z‖^(-2*a):ℝ):ℂ)*F z) =
      ∫ t in Ioi (0:ℝ), ∫ z : ℂ, (rieszGaussianWeight a z t:ℂ)*F z := by
  calc
    _ = ∫ z : ℂ, ∫ t in Ioi (0:ℝ), (rieszGaussianWeight a z t:ℂ)*F z := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_complex_ne_zero] with z hz
      rw [integral_mul_const,integral_complex_ofReal,rieszGaussianWeight_integral ha hz]
      push_cast
      ring
    _ = _ := integral_integral_swap (integrable_riesz_gaussian_product F ha ha1)

end CubicFirstMoment

end

end OAI
