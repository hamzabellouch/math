import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralCoercivity

namespace OAI

/-! Calculus facts for the actual pressure coefficient in the spectral equation. -/

open Set
namespace DefocusingNLS
open ProfileCertificate

theorem radialSpectralPressure_continuous (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) : Continuous (radialSpectralPressure n z) := by
  exact (((radialMatchedProfile_differentiable n z hX hz).continuous.norm).pow _).div_const _

theorem radialSpectralPressure_hasDerivAt (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) :
    HasDerivAt (radialSpectralPressure n z) (deriv (radialSpectralPressure n z) r) r := by
  exact (radialPressure_hasDerivAt _ _ _ r
    (radialMatchedProfile_differentiable n z hX hz r)).differentiableAt.hasDerivAt

theorem radialSpectralPressure_deriv_continuousOn (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) :
    ContinuousOn (deriv (radialSpectralPressure n z)) (Icc 0 R) := by
  exact radialPressure_deriv_continuousOn _ _ _ _
    (radialMatchedProfile_differentiable n z hX hz).continuous.continuousOn
    (radialMatchedProfile_derivative_continuousOn n z hX hz R)
    (fun r _ => radialMatchedProfile_differentiable n z hX hz r)

theorem radialSpectralPressure_nonneg (n : ℕ) (z : ProfileMatchingBall) (r : ℝ) :
    0 ≤ radialSpectralPressure n z r := by
  have ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
  unfold radialSpectralPressure
  positivity

end DefocusingNLS

end OAI
