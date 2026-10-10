import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalFluxIdentity

namespace OAI

/-! The physical flux integral is exactly the imaginary gauge cross pairing. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralCircular_norm_difference (Q f g : ℂ) :
    ‖star Q*(f-Complex.I*g)‖^2-‖Q*(f+Complex.I*g)‖^2 =
      -4*‖Q‖^2*(star g*f).im := by
  rw [norm_mul,norm_mul,norm_star,mul_pow,mul_pow]
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

theorem spectralPhysicalLiouvillePair_gauge_flux_integral
    (a b eta : ℝ) (m : ℕ) (Q : ℝ → ℂ) (lam : ℂ) (F G f g : ℝ → ℂ)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G)
    (he : IsHarmonicRadialEigenpair a b m Q (eta : ℂ) lam F G)
    (hQ : Continuous Q) (hf : Continuous f) (hg : Continuous g)
    (hpair : ∀ r, F r = Q r*(f r+Complex.I*g r) ∧ G r = star (Q r)*(f r-Complex.I*g r))
    (R : ℝ) (hR : 0 < R) :
    spectralScalarFlux (spectralPhysicalLiouvillePair F G R).1+
      spectralScalarFlux (spectralPhysicalLiouvillePair F G R).2 =
      (-4*(a+lam.re-3))*(∫ r in (0 : ℝ)..R,
        (r : ℂ)^11*((‖Q r‖^2 : ℝ) : ℂ)*star (g r)*f r).im := by
  rw [spectralPhysicalLiouvillePair_flux_integral a b eta m Q lam F G hF hG he R hR]
  let C := fun r : ℝ => (r : ℂ)^11*((‖Q r‖^2 : ℝ) : ℂ)*star (g r)*f r
  have hCc : Continuous C := by dsimp only [C]; fun_prop
  have hpoint r : r^11*(‖G r‖^2-‖F r‖^2) = -4*(C r).im := by
    rw [(hpair r).1,(hpair r).2,spectralCircular_norm_difference]
    have hi : (C r).im = r^11*‖Q r‖^2*(star (g r)*f r).im := by
      dsimp only [C]
      rw [mul_assoc,mul_assoc,← Complex.ofReal_pow]
      simp only [Complex.mul_im,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,sub_zero,add_zero]
      ring
    rw [hi]
    ring
  simp_rw [hpoint]
  have hIm : (∫ r in (0 : ℝ)..R, (C r).im) = (∫ r in (0 : ℝ)..R, C r).im :=
    Complex.imCLM.intervalIntegral_comp_comm (hCc.intervalIntegrable 0 R)
  rw [intervalIntegral.integral_const_mul,hIm]
  ring

end DefocusingNLS

end OAI
