import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexScalarAction

namespace OAI

/-! The skew cancellation for the dilation test uses its real constant shift.
This is the pointwise algebra behind the complex virial identity. -/

namespace DefocusingNLS

noncomputable def spectralDilationCross (w s : ℝ) (f g df dg : ℂ) : ℂ :=
  star ((s : ℂ)*g+(w : ℂ)*dg)*f-star ((s : ℂ)*f+(w : ℂ)*df)*g

theorem spectralDilationCross_skew (w s : ℝ) (lam f g df dg : ℂ) :
    (star ((s : ℂ)*f+(w : ℂ)*df)*(-lam*g-(w : ℂ)*dg)+
      star ((s : ℂ)*g+(w : ℂ)*dg)*(lam*f+(w : ℂ)*df)).re =
      ((lam-(s : ℂ))*spectralDilationCross w s f g df dg).re := by
  simp only [spectralDilationCross,Complex.star_def,
    Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
    Complex.neg_re,Complex.neg_im,Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

end DefocusingNLS

end OAI
