import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBPhaseOrder
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarFluxStability

namespace OAI

/-! The selected oscillatory WKB branch has flux of the outgoing sign.
The derivative smallness already used for transfer supplies a fixed margin. -/

namespace DefocusingNLS

theorem spectralComplexSqrt_re_two_thirds (F gamma : ℝ) (hF : 0 < F) :
    (2/3 : ℝ)*‖Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ))‖ ≤
      (Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ))).re := by
  let p := Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ))
  have hr : 0 ≤ p.re := spectralComplexSqrt_re_nonneg _
  have he := congrArg Complex.re (spectralComplexSqrt_sq ((F : ℂ)+Complex.I*(gamma : ℂ)))
  change (p^2).re = ((F : ℂ)+Complex.I*(gamma : ℂ)).re at he
  simp only [pow_two,Complex.mul_re,Complex.add_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_self,add_zero] at he
  have hn : ‖p‖^2 = p.re^2+p.im^2 := by
    simpa only [Complex.normSq_apply,pow_two] using Complex.sq_norm p
  apply (sq_le_sq₀ (by positivity : 0 ≤ (2/3 : ℝ)*‖p‖) hr).mp
  nlinarith [sq_nonneg p.re,sq_nonneg p.im]

theorem spectralWKB_log_flux_margin (h F gamma : ℝ) (v : ℂ)
    (hh : h^2 = 1) (hF : 0 < F)
    (hv : ‖v‖ ≤ ‖Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ))‖^2) :
    ‖Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ))‖/6 ≤
      h*(homogeneousSpectralWKBLog ((h : ℂ)*Complex.I)
        (Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ))) v).im := by
  let p := Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ))
  have hr : (2/3 : ℝ)*‖p‖ ≤ p.re := spectralComplexSqrt_re_two_thirds F gamma hF
  have hp : 0 < ‖p‖ := norm_pos_iff.mpr (spectralComplexSqrt_ne_zero _ (by
    intro hz
    have hzero := congrArg Complex.re hz
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.I_im,
      Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero,Complex.zero_re] at hzero
    linarith))
  have hhabs : |h| = 1 := by nlinarith [sq_abs h,abs_nonneg h]
  have hsmall : ‖v/(2*p)‖ ≤ ‖p‖/2 := by
    rw [norm_div,norm_mul]
    norm_num only [Complex.norm_ofNat]
    apply (div_le_iff₀ (by positivity : 0 < 2*‖p‖)).mpr
    nlinarith
  have hi : h*(v/(2*p)).im ≤ ‖p‖/2 := by
    calc
      _ ≤ |h*(v/(2*p)).im| := le_abs_self _
      _ = |(v/(2*p)).im| := by rw [abs_mul,hhabs,one_mul]
      _ ≤ ‖v/(2*p)‖ := Complex.abs_im_le_norm _
      _ ≤ _ := hsmall
  have he : h*(homogeneousSpectralWKBLog ((h : ℂ)*Complex.I) p v).im =
      p.re - h*(v/(2*p)).im := by
    simp only [homogeneousSpectralWKBLog,Complex.sub_im,Complex.mul_im,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
      zero_add,add_zero,mul_one,sub_zero]
    nlinarith [hh]
  rw [he]
  linarith

end DefocusingNLS

end OAI
