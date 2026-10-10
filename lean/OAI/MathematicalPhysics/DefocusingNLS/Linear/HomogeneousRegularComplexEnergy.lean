import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRegularEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGaugeAngular

namespace OAI

/-! # Complex radial energy and the small-ball Poincaré bound -/

open Set MeasureTheory
open scoped ContDiff
namespace DefocusingNLS

theorem homogeneousRegular_complex_poincare (R : ℝ) (hR : 0 ≤ R)
    (F : ℝ → ℂ) (hF : ContDiff ℝ 1 F) (hFR : F R = 0) :
    16 * (∫ r in (0 : ℝ)..R, r ^ 11 * ‖F r‖ ^ 2) ≤
      R ^ 2 * (∫ r in (0 : ℝ)..R, r ^ 11 * ‖deriv F r‖ ^ 2) := by
  have hr := homogeneousRegular_poincare R hR (fun r => (F r).re)
    (Complex.reCLM.contDiff.comp hF) (by rw [hFR]; rfl)
  have hi := homogeneousRegular_poincare R hR (fun r => (F r).im)
    (Complex.imCLM.contDiff.comp hF) (by rw [hFR]; rfl)
  have hdre : deriv (fun r => (F r).re) = fun r => (deriv F r).re := by
    funext r
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt r
      (hF.differentiable (by norm_num) r).hasDerivAt).deriv
  have hdim : deriv (fun r => (F r).im) = fun r => (deriv F r).im := by
    funext r
    exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt r
      (hF.differentiable (by norm_num) r).hasDerivAt).deriv
  rw [hdre] at hr
  rw [hdim] at hi
  have hnorm (G : ℝ → ℂ) (hG : Continuous G) :
      (∫ r in (0 : ℝ)..R, r ^ 11 * ‖G r‖ ^ 2) =
        (∫ r in (0 : ℝ)..R, r ^ 11 * (G r).re ^ 2) +
        (∫ r in (0 : ℝ)..R, r ^ 11 * (G r).im ^ 2) := by
    have hpoint (r : ℝ) : r ^ 11 * ‖G r‖ ^ 2 =
        r ^ 11 * (G r).re ^ 2 + r ^ 11 * (G r).im ^ 2 := by
      rw [Complex.sq_norm]
      simp only [Complex.normSq_apply]
      ring
    simp_rw [hpoint]
    rw [intervalIntegral.integral_add]
    · exact Continuous.intervalIntegrable (by fun_prop) 0 R
    · exact Continuous.intervalIntegrable (by fun_prop) 0 R
  rw [hnorm F hF.continuous, hnorm (deriv F) hF.continuous_deriv_one]
  linarith

theorem homogeneousRegular_complex_energy (R eta : ℝ) (hR : 0 ≤ R)
    (F H : ℝ → ℂ) (hF : ContDiff ℝ 2 F) (hH : Continuous H) (hFR : F R = 0)
    (hODE : ∀ r, 0 < r → r ≤ R → deriv (deriv F) r +
      ((11 / r : ℝ) : ℂ) * deriv F r - ((eta / r ^ 2 : ℝ) : ℂ) * F r = H r) :
    (∫ r in (0 : ℝ)..R, r ^ 11 * ‖deriv F r‖ ^ 2) +
      eta * (∫ r in (0 : ℝ)..R, r ^ 9 * ‖F r‖ ^ 2) =
        -(∫ r in (0 : ℝ)..R, r ^ 11 * (star (F r) * H r).re) := by
  obtain ⟨hdr, hddr⟩ := homogeneousCoordinate_derivatives F hF Complex.reCLM
  obtain ⟨hdi, hddi⟩ := homogeneousCoordinate_derivatives F hF Complex.imCLM
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hdr hddr hdi hddi
  have hre : ∀ r, 0 < r → r ≤ R →
      deriv (deriv (fun r => (F r).re)) r + 11 / r * deriv (fun r => (F r).re) r -
        eta / r ^ 2 * (F r).re = (H r).re := by
    intro r hr hrr
    rw [hddr, hdr]
    simpa only [Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      congrArg Complex.re (hODE r hr hrr)
  have him : ∀ r, 0 < r → r ≤ R →
      deriv (deriv (fun r => (F r).im)) r + 11 / r * deriv (fun r => (F r).im) r -
        eta / r ^ 2 * (F r).im = (H r).im := by
    intro r hr hrr
    rw [hddi, hdi]
    simpa only [Complex.add_im, Complex.sub_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using
      congrArg Complex.im (hODE r hr hrr)
  have hr := homogeneousRegular_energy_identity R eta hR (fun r => (F r).re)
    (fun r => (H r).re) (Complex.reCLM.contDiff.comp hF) (Complex.continuous_re.comp hH) (by rw [hFR]; rfl) hre
  have hi := homogeneousRegular_energy_identity R eta hR (fun r => (F r).im)
    (fun r => (H r).im) (Complex.imCLM.contDiff.comp hF) (Complex.continuous_im.comp hH) (by rw [hFR]; rfl) him
  rw [hdr] at hr
  rw [hdi] at hi
  have hs : (∫ r in (0 : ℝ)..R, r ^ 11 * (star (F r) * H r).re) =
      (∫ r in (0 : ℝ)..R, r ^ 11 * (F r).re * (H r).re) +
      (∫ r in (0 : ℝ)..R, r ^ 11 * (F r).im * (H r).im) := by
    have he (r : ℝ) : r ^ 11 * (star (F r) * H r).re =
        r ^ 11 * (F r).re * (H r).re + r ^ 11 * (F r).im * (H r).im := by
      simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    simp_rw [he]
    rw [intervalIntegral.integral_add]
    · exact Continuous.intervalIntegrable (by fun_prop) 0 R
    · exact Continuous.intervalIntegrable (by fun_prop) 0 R
  have hn (G : ℝ → ℂ) (hG : Continuous G) (k : ℕ) :
      (∫ r in (0 : ℝ)..R, r ^ k * ‖G r‖ ^ 2) =
        (∫ r in (0 : ℝ)..R, r ^ k * (G r).re ^ 2) +
        (∫ r in (0 : ℝ)..R, r ^ k * (G r).im ^ 2) := by
    have he (r : ℝ) : r ^ k * ‖G r‖ ^ 2 =
        r ^ k * (G r).re ^ 2 + r ^ k * (G r).im ^ 2 := by
      rw [Complex.sq_norm]
      simp only [Complex.normSq_apply]
      ring
    simp_rw [he]
    rw [intervalIntegral.integral_add]
    · exact Continuous.intervalIntegrable (by fun_prop) 0 R
    · exact Continuous.intervalIntegrable (by fun_prop) 0 R
  rw [hn (deriv F) (hF.continuous_deriv (by norm_num)) 11, hn F hF.continuous 9, hs]
  linarith

end DefocusingNLS

end OAI
