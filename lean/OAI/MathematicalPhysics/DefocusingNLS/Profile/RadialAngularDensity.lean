import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVelocityCalculus

namespace OAI

/-! Regular weighted angular coefficients at the radial origin. -/

open Set
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialAngularDensity (n : ℕ) (z : ProfileMatchingBall) (r : ℝ) : ℝ :=
  r^9*‖radialMatchedProfile n z r‖^2

noncomputable def radialAngularSlope (n : ℕ) (z : ProfileMatchingBall) (r : ℝ) : ℝ :=
  9*r^8*‖radialMatchedProfile n z r‖^2+
    2*r^9*(star (radialMatchedProfile n z r)*deriv (radialMatchedProfile n z) r).re

noncomputable def radialMatchedVelocityRatio (n : ℕ) (z : ProfileMatchingBall) : ℝ → ℝ :=
  radialVelocityRatio (6-2*radialShootingA n) (fun r => ‖radialMatchedProfile n z r‖)

theorem radialAngularDensity_continuous (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) : Continuous (radialAngularDensity n z) := by
  exact (continuous_id.pow 9).mul
    ((radialMatchedProfile_differentiable n z hX hz).continuous.norm.pow 2)

theorem radialAngularDensity_hasDerivAt (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) :
    HasDerivAt (radialAngularDensity n z) (radialAngularSlope n z r) r := by
  have h := ((hasDerivAt_id r).pow 9).mul
    (radialComplexNormSq_hasDerivAt (radialMatchedProfile n z) r
      (radialMatchedProfile_differentiable n z hX hz r))
  convert h using 1
  · funext t
    simp only [radialAngularDensity,Pi.mul_apply,Pi.pow_apply,id_eq,Complex.sq_norm]
  · simp only [radialAngularSlope,Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,mul_one,
      Complex.sq_norm]
    ring

theorem radialMatchedVelocityRatio_continuousOn (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) :
    ContinuousOn (radialMatchedVelocityRatio n z) (Icc 0 R) := by
  have hA := (radialMatchedProfile_differentiable n z hX hz).continuous.norm
  exact ((continuous_const.mul (continuous_radialAverage _ (hA.pow 2))).continuousOn.div
    (hA.pow 2).continuousOn (by
      intro r hr
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr
        (radialMatchedProfile_ne_zero n z hX r hr.1))))

theorem radialMatchedVelocity_eq_mul_ratio (n : ℕ) (z : ProfileMatchingBall) (r : ℝ) :
    radialMatchedVelocity n z r=r*radialMatchedVelocityRatio n z r := rfl

theorem radialAngularFlux_hasDerivAt (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (fun t => radialAngularDensity n z t*radialMatchedVelocity n z t)
      ((6-2*radialShootingA n-2*radialMatchedVelocityRatio n z r)*radialAngularDensity n z r) r := by
  have h := (radialAngularDensity_hasDerivAt n z hX hz r).mul
    (radialMatchedVelocity_differentiableAt n z hX hz r hr).hasDerivAt
  apply h.congr_deriv
  apply mul_left_cancel₀ (pow_ne_zero 2 hr.ne')
  have hM := radialMassSlope_velocity n z hX hz r hr.le
  have hK : r^2*radialAngularDensity n z r=radialMassDensity n z r := by
    unfold radialAngularDensity radialMassDensity
    ring
  have hS : r^2*radialAngularSlope n z r=
      radialMassSlope n z r-2*r*radialAngularDensity n z r := by
    unfold radialAngularSlope radialMassSlope radialAngularDensity
    ring
  calc
    r^2*(radialAngularSlope n z r*radialMatchedVelocity n z r+
        radialAngularDensity n z r*deriv (radialMatchedVelocity n z) r) =
        (r^2*radialAngularSlope n z r)*radialMatchedVelocity n z r+
        (r^2*radialAngularDensity n z r)*deriv (radialMatchedVelocity n z) r := by ring
    _ = (6-2*radialShootingA n)*radialMassDensity n z r-
        2*r*radialAngularDensity n z r*radialMatchedVelocity n z r := by
      rw [hS,hK]
      linear_combination hM
    _ = r^2*((6-2*radialShootingA n-2*radialMatchedVelocityRatio n z r)*
        radialAngularDensity n z r) := by
      rw [← hK,radialMatchedVelocity_eq_mul_ratio]
      ring

end DefocusingNLS

end OAI
