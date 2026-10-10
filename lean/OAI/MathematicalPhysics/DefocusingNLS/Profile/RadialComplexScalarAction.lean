import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialAngularScalar

namespace OAI

/-! Complexification of the existing radial scalar action and test.
The real and imaginary components retain the checked integration identities. -/

namespace DefocusingNLS
open ProfileCertificate

theorem radialComplex_deriv_re (f : ℝ → ℂ) (hf : Differentiable ℝ f) :
    deriv (fun r => (f r).re) = fun r => (deriv f r).re := by
  funext r
  exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (hf r).hasDerivAt).deriv

theorem radialComplex_deriv_im (f : ℝ → ℂ) (hf : Differentiable ℝ f) :
    deriv (fun r => (f r).im) = fun r => (deriv f r).im := by
  funext r
  exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt r (hf r).hasDerivAt).deriv

noncomputable def radialComplexAngularAction (n : ℕ) (z : ProfileMatchingBall) (eta : ℝ)
    (q : ℝ → ℝ) (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  -(radialMassDensity n z r : ℂ)*deriv (deriv f) r-
    (radialMassSlope n z r : ℂ)*deriv f r+
    (radialMassDensity n z r*q r+eta*radialAngularDensity n z r : ℝ)*f r

noncomputable def radialComplexTest (n : ℕ) (z : ProfileMatchingBall) (s : ℝ)
    (f : ℝ → ℂ) (r : ℝ) : ℂ := (s : ℂ)*f r+(radialMatchedVelocity n z r : ℂ)*deriv f r

theorem radialComplexAngularAction_re (n : ℕ) (z : ProfileMatchingBall) (eta : ℝ)
    (q : ℝ → ℝ) (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (r : ℝ) :
    (radialComplexAngularAction n z eta q f r).re =
      radialAngularScalarAction n z eta q (fun t => (f t).re) r := by
  have hd := radialComplex_deriv_re f (hf.differentiable (by norm_num))
  have hfd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hdd := radialComplex_deriv_re (deriv f) (hfd.differentiable (by norm_num))
  simp only [radialComplexAngularAction,radialAngularScalarAction,radialScalarAction,
    radialMassLaplacian,hd,hdd,Complex.add_re,Complex.sub_re,Complex.mul_re,
    Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

theorem radialComplexAngularAction_im (n : ℕ) (z : ProfileMatchingBall) (eta : ℝ)
    (q : ℝ → ℝ) (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (r : ℝ) :
    (radialComplexAngularAction n z eta q f r).im =
      radialAngularScalarAction n z eta q (fun t => (f t).im) r := by
  have hd := radialComplex_deriv_im f (hf.differentiable (by norm_num))
  have hfd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hdd := radialComplex_deriv_im (deriv f) (hfd.differentiable (by norm_num))
  simp only [radialComplexAngularAction,radialAngularScalarAction,radialScalarAction,
    radialMassLaplacian,hd,hdd,Complex.add_im,Complex.sub_im,Complex.mul_im,
    Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  ring

theorem radialComplexTest_re (n : ℕ) (z : ProfileMatchingBall) (s : ℝ)
    (f : ℝ → ℂ) (hf : Differentiable ℝ f) (r : ℝ) :
    (radialComplexTest n z s f r).re = radialSpectralTest n z s 0
      (fun t => (f t).re) (fun t => (f t).re) r := by
  simp only [radialComplexTest,radialSpectralTest,radialComplex_deriv_re f hf,
    Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]

theorem radialComplexTest_im (n : ℕ) (z : ProfileMatchingBall) (s : ℝ)
    (f : ℝ → ℂ) (hf : Differentiable ℝ f) (r : ℝ) :
    (radialComplexTest n z s f r).im = radialSpectralTest n z s 0
      (fun t => (f t).im) (fun t => (f t).im) r := by
  simp only [radialComplexTest,radialSpectralTest,radialComplex_deriv_im f hf,
    Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]

end DefocusingNLS

end OAI
