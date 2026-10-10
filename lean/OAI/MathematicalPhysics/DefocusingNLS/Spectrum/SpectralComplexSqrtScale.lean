import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBPhaseOrder

namespace OAI

/-! Positive dilation commutes with the selected momentum square root in
the right half-plane. -/

namespace DefocusingNLS

theorem spectralComplexSqrt_scale (d : ℝ) (hd : 0 < d) (z : ℂ) (hz : 0 < z.re) :
    Complex.sqrt ((d : ℂ)^2*z) = (d : ℂ)*Complex.sqrt z := by
  have hzrep : (z.re : ℂ)+Complex.I*(z.im : ℂ) = z := by
    apply Complex.ext <;> simp
  have hp : 0 < (Complex.sqrt z).re := by
    simpa only [hzrep] using spectralComplexSqrt_re_pos z.re z.im hz
  have hs : (Complex.sqrt ((d : ℂ)^2*z))^2 = ((d : ℂ)*Complex.sqrt z)^2 := by
    rw [spectralComplexSqrt_sq,mul_pow,spectralComplexSqrt_sq]
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hs with he | he
  · exact he
  · have hn := spectralComplexSqrt_re_nonneg ((d : ℂ)^2*z)
    rw [he,Complex.neg_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hn
    nlinarith

end DefocusingNLS

end OAI
