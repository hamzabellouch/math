import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeGaugeCoefficient

namespace OAI

/-! The two physical free gauge profiles and their conjugate equations. -/

namespace DefocusingNLS
open ProfileCertificate

theorem radialShootingFreeExterior_equation (z : ProfileMatchingBall) (r : ℝ) (hr : 0 < r) :
    deriv (deriv (radialShootingFreeExterior z)) r+
      (11/(r : ℂ)+Complex.I*(r : ℂ)/2)*deriv (radialShootingFreeExterior z) r+
      (radialShootingB (profileMatchingParameter z) : ℂ)*radialShootingFreeExterior z r=0 := by
  rw [(radialShootingFreeExterior_hasDerivAt_deriv z r hr).deriv]
  dsimp only [radialFreeCoefficient]
  push_cast
  ring

theorem radialShootingFreeConjugate_equation (z : ProfileMatchingBall) (r : ℝ) (hr : 0 < r) :
    deriv (deriv (fun t => star (radialShootingFreeExterior z t))) r+
      (11/(r : ℂ)-Complex.I*(r : ℂ)/2)*
        deriv (fun t => star (radialShootingFreeExterior z t)) r+
      (radialShootingB (profileMatchingParameter z) : ℂ)*star (radialShootingFreeExterior z r)=0 := by
  have he := congrArg star (radialShootingFreeExterior_equation z r hr)
  rw [deriv.star',deriv.star']
  simpa [sub_eq_add_neg,neg_div] using he

theorem radialMatchedFreeConjugateGaugeCoefficient (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (r : ℝ)
    (hr : radialShootingR (profileMatchingParameter z) ≤ r) :
    (((2*(star (radialShootingFreeExterior z r)*deriv (radialShootingFreeExterior z) r).re : ℝ) : ℂ)-
        Complex.I*(radialMatchedFreeTransportFunction z r : ℂ))*star (radialShootingFreeExterior z r)=
      (radialMatchedFreeMassFunction z r : ℂ)*
        (2*star (deriv (radialShootingFreeExterior z) r)-
          Complex.I*(r/2 : ℝ)*star (radialShootingFreeExterior z r)) := by
  have he := congrArg star (radialMatchedFreeGaugeCoefficient z hz₁ hz hc r hr)
  simpa [sub_eq_add_neg] using he

end DefocusingNLS

end OAI
