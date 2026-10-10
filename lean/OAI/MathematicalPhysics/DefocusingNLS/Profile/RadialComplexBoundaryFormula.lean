import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexVirial

namespace OAI

/-! The summed real boundary forms have the usual complex norm expression. -/

namespace DefocusingNLS
open ProfileCertificate

theorem radialComplexAngularBoundary_eq (n : ℕ) (z : ProfileMatchingBall)
    (eta R s : ℝ) (q : ℝ → ℝ) (f : ℝ → ℂ) (hf : Differentiable ℝ f) :
    radialComplexAngularBoundary n z eta R s q f =
      (radialMassFlux n z R/2)*(q R*‖f R‖^2-‖deriv f R‖^2)-
      radialMassDensity n z R*s*(star (f R)*deriv f R).re+
      (eta*radialAngularDensity n z R*radialMatchedVelocity n z R/2)*‖f R‖^2 := by
  unfold radialComplexAngularBoundary radialAngularScalarBoundary radialSpectralBoundary radialAngularBoundary
  rw [radialComplex_deriv_re f hf,radialComplex_deriv_im f hf]
  simp only [Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im,
    Complex.sq_norm,Complex.normSq_apply]
  ring

end DefocusingNLS

end OAI
