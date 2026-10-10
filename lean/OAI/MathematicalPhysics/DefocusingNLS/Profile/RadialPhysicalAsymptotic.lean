import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCartesianSmooth
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPhysicalFactor

namespace OAI

/-! The exact leading modulus of the matched physical radial profile at infinity. -/

open Filter Set
namespace DefocusingNLS
open ProfileCertificate

theorem radialPhysicalExterior_scaled_norm (ν : ℂ) (Z : ℝ → ℂ × ℂ)
    (r : ℝ) (hr : 0 < r) :
    r^(-ν.re)*‖radialPhysicalExterior ν Z r‖ = ‖(Z (Real.log r)).1‖ := by
  rw [radialPhysicalExterior,norm_mul,radialPhysicalFactor_norm ν r hr,
    ← mul_assoc,← Real.rpow_add hr,neg_add_cancel,Real.rpow_zero,one_mul]

theorem radialMatchedProfile_scaled_norm_tendsto (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius)) :
    Tendsto (fun r : ℝ => r^(2*radialShootingA n)*‖radialMatchedProfile n z r‖)
      atTop (nhds ‖radialShootingM z‖) := by
  let ν := radialShootingNu (n+radialInnerShootingThreshold) z
  let Z := radialExteriorCanonical ν (n+radialInnerShootingThreshold)
    (radialShootingM z) (Real.log innerBoundaryRadius)
  have hZ : Tendsto Z atTop (nhds (radialShootingM z,0)) :=
    (radialExteriorCanonical_spec hX).2.1.tendsto
  have hZ1 : Tendsto (fun t => (Z t).1) atTop (nhds (radialShootingM z)) :=
    (continuous_fst.tendsto (radialShootingM z,(0 : ℂ))).comp hZ
  have ht : Tendsto (fun r : ℝ => ‖(Z (Real.log r)).1‖) atTop
      (nhds ‖radialShootingM z‖) := hZ1.norm.comp Real.tendsto_log_atTop
  apply ht.congr'
  filter_upwards [eventually_gt_atTop innerBoundaryRadius,eventually_gt_atTop (0 : ℝ)] with r hr hr0
  have hν : -ν.re=2*radialShootingA n := by
    dsimp only [ν]
    rw [radialShootingNu_physical]
    simp
  rw [← radialPhysicalExterior_scaled_norm ν Z r hr0,hν]
  congr 2
  simp only [radialMatchedProfile,ite_eq_right (not_le.mpr hr),radialShootingExteriorProfile,ν,Z]

end DefocusingNLS

end OAI
