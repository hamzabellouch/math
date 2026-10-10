import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPhysicalAsymptotic

namespace OAI

/-! The first radial derivative has the precise physical symbol order. -/

open Filter Set
namespace DefocusingNLS
open ProfileCertificate

theorem radialPhysicalExteriorSlope_scaled_norm (ν : ℂ) (Z : ℝ → ℂ × ℂ)
    (r : ℝ) (hr : 0 < r) :
    r^(1-ν.re)*‖radialPhysicalExteriorSlope ν Z r‖ =
      ‖ν*(Z (Real.log r)).1+(Z (Real.log r)).2‖ := by
  rw [radialPhysicalExteriorSlope,norm_mul,norm_div,radialPhysicalFactor_norm ν r hr,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,Real.rpow_sub hr,Real.rpow_one]
  have hp : r^ν.re ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hr _)
  field_simp

theorem radialMatchedProfile_scaled_deriv_tendsto (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) :
    Tendsto (fun r : ℝ => r^(2*radialShootingA n+1)*‖deriv (radialMatchedProfile n z) r‖)
      atTop (nhds ‖radialShootingNu (n+radialInnerShootingThreshold) z*radialShootingM z‖) := by
  let ν := radialShootingNu (n+radialInnerShootingThreshold) z
  let Z := radialExteriorCanonical ν (n+radialInnerShootingThreshold)
    (radialShootingM z) (Real.log innerBoundaryRadius)
  have hZ : Tendsto Z atTop (nhds (radialShootingM z,0)) :=
    (radialExteriorCanonical_spec hX).2.1.tendsto
  have hZ1 : Tendsto (fun t => (Z t).1) atTop (nhds (radialShootingM z)) :=
    (continuous_fst.tendsto (radialShootingM z,(0 : ℂ))).comp hZ
  have hZ2 : Tendsto (fun t => (Z t).2) atTop (nhds (0 : ℂ)) :=
    (continuous_snd.tendsto (radialShootingM z,(0 : ℂ))).comp hZ
  have ht : Tendsto (fun r : ℝ => ‖ν*(Z (Real.log r)).1+(Z (Real.log r)).2‖)
      atTop (nhds ‖ν*radialShootingM z‖) := by
    simpa only [add_zero,Function.comp_def] using ((hZ1.const_mul ν).add hZ2).norm.comp Real.tendsto_log_atTop
  apply ht.congr'
  filter_upwards [eventually_gt_atTop innerBoundaryRadius,eventually_gt_atTop (0 : ℝ)] with r hr hr0
  have hν : 1-ν.re=2*radialShootingA n+1 := by
    dsimp only [ν]
    rw [radialShootingNu_physical]
    simp
    ring
  have hd : deriv (radialMatchedProfile n z) r=radialPhysicalExteriorSlope ν Z r := by
    rw [(radialMatchedProfile_hasDerivAt n z hX hz r hr0).deriv]
    simp only [radialMatchedJet,ite_eq_right (not_le.mpr hr),radialShootingPhysicalJet,
      radialPhysicalJet,ν,Z]
  rw [hd,← hν]
  exact (radialPhysicalExteriorSlope_scaled_norm ν Z r hr0).symm

end DefocusingNLS

end OAI
