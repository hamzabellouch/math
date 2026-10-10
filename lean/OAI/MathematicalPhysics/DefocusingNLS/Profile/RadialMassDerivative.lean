import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMassDivergence

namespace OAI

/-! Nonsingular derivative of the radial mass density and its logarithmic form. -/

open Set
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialMassSlope (n : ℕ) (z : ProfileMatchingBall) (r : ℝ) : ℝ :=
  11*r^10*‖radialMatchedProfile n z r‖^2+
    2*r^11*(star (radialMatchedProfile n z r)*deriv (radialMatchedProfile n z) r).re

theorem radialMassDensity_hasDerivAt (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) :
    HasDerivAt (radialMassDensity n z) (radialMassSlope n z r) r := by
  have h := ((hasDerivAt_id r).pow 11).mul
    (radialComplexNormSq_hasDerivAt (radialMatchedProfile n z) r
      (radialMatchedProfile_differentiable n z hX hz r))
  convert h using 1
  · funext t
    simp only [radialMassDensity,Pi.mul_apply,Pi.pow_apply,id_eq,Complex.sq_norm]
  · simp only [radialMassSlope,Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,mul_one,
      Complex.sq_norm]
    ring

theorem radialMassSlope_continuousOn (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) :
    ContinuousOn (radialMassSlope n z) (Icc 0 R) := by
  have hQ := (radialMatchedProfile_differentiable n z hX hz).continuous
  have hD := radialMatchedProfile_derivative_continuousOn n z hX hz R
  have hJ := Complex.continuous_re.comp_continuousOn (hQ.continuousOn.star.mul hD)
  exact (((continuous_const.mul (continuous_id.pow 10)).mul (hQ.norm.pow 2)).continuousOn).add
    ((continuous_const.mul (continuous_id.pow 11)).continuousOn.mul hJ)

theorem radialMassSlope_logarithmic (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (r : ℝ) (hr : 0 < r) :
    radialMassSlope n z r=
      (11/r+2*(deriv (radialMatchedProfile n z) r/radialMatchedProfile n z r).re)*
        radialMassDensity n z r := by
  have hN := (Complex.normSq_pos.mpr (radialMatchedProfile_ne_zero n z hX r hr.le)).ne'
  rw [complex_logDerivative_re]
  unfold radialMassSlope radialMassDensity
  simp only [Complex.sq_norm]
  field_simp [hr.ne',hN]

end DefocusingNLS

end OAI
