import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorVelocity

namespace OAI

/-! Exact weighted pressure in terms of the outgoing canonical amplitude. -/

namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_exterior_pressure (n : ℕ) (z : ProfileMatchingBall)
    (r : ℝ) (hr : innerBoundaryRadius < r) :
    let m := n+radialInnerShootingThreshold
    let Z := radialExteriorCanonical (radialShootingNu m z) m (radialShootingM z)
      (Real.log innerBoundaryRadius)
    r^2*(‖radialMatchedProfile n z r‖^(2*m)/radialShootingA n)=
      2*(m : ℝ)*‖(Z (Real.log r)).1‖^(2*m) := by
  intro m Z
  have hrp : 0 < r := lt_trans (by linarith [innerBoundaryRadius_bounds.1]) hr
  have hmp : 0 < m := radialShootingInner_power_pos n (profileMatchingParameter z)
  have hν : radialShootingNu m z=
      -1/(m : ℂ)+2*Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ) := by
    unfold radialShootingNu radialShootingQ
    ring
  have he : ‖radialMatchedProfile n z r‖^(2*m)=
      (1/r^2)*‖(Z (Real.log r)).1‖^(2*m) := by
    simp only [radialMatchedProfile,ite_eq_right hr.not_ge,radialShootingExteriorProfile,
      radialPhysicalExterior,norm_mul,mul_pow]
    rw [hν,radialPhysicalFactor_norm_power m hmp _ r hrp]
    simp only [Z,hν,m]
  rw [he]
  unfold radialShootingA
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hmp.ne'
  change r^2*((1/r^2)*‖(Z (Real.log r)).1‖^(2*m)/(1/(2*(m : ℝ))))=_
  field_simp [hrp.ne',hm0]

end DefocusingNLS

end OAI
