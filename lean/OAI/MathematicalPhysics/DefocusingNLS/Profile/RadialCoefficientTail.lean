import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVelocityTail
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralCoercivity

namespace OAI

/-! Polynomial bounds for every actual coefficient in the outgoing energy trace. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_coefficient_tail :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ᶠ r : ℝ in atTop,
      0 ≤ radialMassDensity n z r ∧ radialMassDensity n z r ≤ 144*r^11 ∧
      |radialMassFlux n z r| ≤ 144*r^12 ∧
      0 ≤ radialSpectralPressure n z r ∧ radialSpectralPressure n z r ≤ 1/radialShootingA n ∧
      0 ≤ radialHardyFlux (radialShootingA n) r ∧ radialHardyFlux (radialShootingA n) r ≤ r^10 := by
  obtain ⟨d,hd,hW⟩ := radialMatched_uniform_weight_comparison
  filter_upwards [hW,radialMatched_global_pressure_bound] with n hwn hpn z hX hz
  have ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
  filter_upwards [radialMatchedVelocity_eventually_bound n z hX hz,
    eventually_gt_atTop (0 : ℝ)] with r hwr hr
  have hρ : radialHardyWeight (radialShootingA n) r ≤ 1 := by
    unfold radialHardyWeight
    exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg r]) (by linarith)
  have hμ : ‖radialMatchedProfile n z r‖^2 ≤ 144 := by
    have hh := (hwn z r hr.le).2
    change ‖radialMatchedProfile n z r‖^2 ≤ 144*radialHardyWeight (radialShootingA n) r at hh
    linarith
  have hM0 : 0 ≤ radialMassDensity n z r := by
    unfold radialMassDensity
    positivity
  have hM : radialMassDensity n z r ≤ 144*r^11 := by
    unfold radialMassDensity
    nlinarith [mul_le_mul_of_nonneg_left hμ (pow_nonneg hr.le 11)]
  have hF : |radialMassFlux n z r| ≤ 144*r^12 := by
    change |radialMassDensity n z r*radialMatchedVelocity n z r| ≤ _
    rw [abs_mul,abs_of_nonneg hM0]
    calc
      _ ≤ radialMassDensity n z r*r := mul_le_mul_of_nonneg_left hwr hM0
      _ ≤ (144*r^11)*r := mul_le_mul_of_nonneg_right hM hr.le
      _ = _ := by ring
  have hP0 : 0 ≤ radialSpectralPressure n z r := by
    unfold radialSpectralPressure
    positivity
  have hP : radialSpectralPressure n z r ≤ 1/radialShootingA n := by
    exact (div_le_div_iff_of_pos_right ha).mpr (hpn z r hr.le)
  have hH0 : 0 ≤ radialHardyFlux (radialShootingA n) r := by
    unfold radialHardyFlux
    exact mul_nonneg (pow_nonneg hr.le 10) (radialHardyWeight_pos _ _).le
  have hH : radialHardyFlux (radialShootingA n) r ≤ r^10 := by
    simpa only [radialHardyFlux,mul_one] using mul_le_mul_of_nonneg_left hρ (pow_nonneg hr.le 10)
  exact ⟨hM0,hM,hF,hP0,hP,hH0,hH⟩

end DefocusingNLS

end OAI
