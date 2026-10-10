import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialGreenEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformDeformation

namespace OAI

/-! Regularity of the actual radial velocity and its weighted derivative identity. -/

open Set Filter
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedVelocity_continuousOn (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) :
    ContinuousOn (radialMatchedVelocity n z) (Icc 0 R) := by
  have hA := (radialMatchedProfile_differentiable n z hX hz).continuous.norm
  have hav := continuous_radialAverage _ (hA.pow 2)
  exact continuous_id.continuousOn.mul
    ((continuous_const.mul hav).continuousOn.div (hA.pow 2).continuousOn (by
      intro r hr
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr
        (radialMatchedProfile_ne_zero n z hX r hr.1))))

theorem radialMatchedVelocity_differentiableAt (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : 0 < r) :
    DifferentiableAt ℝ (radialMatchedVelocity n z) r := by
  have hA := (radialMatchedProfile_differentiable n z hX hz).continuous.norm
  have hdA := (((radialMatchedAmplitude_contDiffOn n z hX hz) r hr).contDiffAt
    (Ioi_mem_nhds hr)).differentiableAt (by simp)
  exact differentiableAt_id.mul
    (((differentiableAt_const _).mul
      (hasDerivAt_radialAverage _ (hA.pow 2) r hr.ne').differentiableAt).div
        (hdA.pow 2) (pow_ne_zero 2 (norm_ne_zero_iff.mpr
          (radialMatchedProfile_ne_zero n z hX r hr.le))))

theorem radialMassSlope_velocity (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : 0 ≤ r) :
    radialMassSlope n z r*radialMatchedVelocity n z r+
      radialMassDensity n z r*deriv (radialMatchedVelocity n z) r=
        (6-2*radialShootingA n)*radialMassDensity n z r := by
  rcases hr.eq_or_lt with he | hp
  · subst r
    simp [radialMassSlope,radialMassDensity]
  · have h := (radialMassDensity_hasDerivAt n z hX hz r).mul
      (radialMatchedVelocity_differentiableAt n z hX hz r hp).hasDerivAt
    have hf := radialMassFlux_hasDerivAt n z hX hz r hp
    exact h.unique hf

end DefocusingNLS

end OAI
