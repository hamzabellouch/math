import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorPressureIdentity

namespace OAI

/-! The exact Euler derivative of the exterior pressure. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_exterior_pressure_derivative (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : innerBoundaryRadius < r) :
    let m := n+radialInnerShootingThreshold
    let Z := radialExteriorCanonical (radialShootingNu m z) m (radialShootingM z)
      (Real.log innerBoundaryRadius)
    let ξ := (Z (Real.log r)).2/(Z (Real.log r)).1
    let P := fun t => ‖radialMatchedProfile n z t‖^(2*m)/radialShootingA n
    r*deriv P r=P r*(-2+2*(m : ℝ)*ξ.re) := by
  intro m Z ξ P
  let A := fun t => ‖radialMatchedProfile n z t‖
  let ν := radialShootingNu m z
  have hrp : 0 < r := lt_trans (by linarith [innerBoundaryRadius_bounds.1]) hr
  have hmp : 0 < m := radialShootingInner_power_pos n (profileMatchingParameter z)
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hmp.ne'
  have hAr : A r ≠ 0 := norm_ne_zero_iff.mpr
    (radialMatchedProfile_ne_zero n z hX r hrp.le)
  have hAs := ((radialMatchedAmplitude_contDiffOn n z hX hz) r hrp).contDiffAt
    (Ioi_mem_nhds hrp)
  have hdA : HasDerivAt A (deriv A r) r := (hAs.differentiableAt (by simp)).hasDerivAt
  have hlog := radialMatchedAmplitude_logDerivative n z hX hz r hrp
  rw [radialMatchedProfile_logDerivative n z hX hz r hr] at hlog
  simp only [Complex.div_ofReal_re] at hlog
  change deriv A r/A r=(ν+ξ).re/r at hlog
  have hpower : (A r)^(2*m-1)=(A r)^(2*m)/A r := by
    apply (eq_div_iff hAr).2
    rw [← pow_succ]
    congr 1
    omega
  have hdP := (hdA.pow (2*m)).div_const (radialShootingA n)
  change HasDerivAt P _ r at hdP
  have he : deriv P r=P r*(2*(m : ℝ))*(deriv A r/A r) := by
    rw [hdP.deriv,hpower]
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    dsimp only [P,A]
    ring
  have hν : ν.re= -1/(m : ℝ) := by
    dsimp [ν,radialShootingNu,radialShootingQ]
    simp [Complex.mul_re,Complex.mul_im]
    ring
  rw [he,hlog,Complex.add_re,hν]
  field_simp [hrp.ne',hm0]

end DefocusingNLS

end OAI
