import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformAnnulus
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorPressureIdentity
import Mathlib.Analysis.SpecificLimits.Normed
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedInnerAmplitude
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedProfileBounds

namespace OAI

/-! The actual exterior pressure is uniformly small after multiplication by r². -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_exterior_pressure_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall, ∀ r : ℝ, innerBoundaryRadius < r →
      r^2*(‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold))/
        radialShootingA n) < ε := by
  obtain ⟨κ,ρ,_hκ,hρ,hann⟩ := radialShooting_uniform_annulus
  let q := max ρ 0
  have hq : 0 ≤ q := le_max_right _ _
  have hq1 : q < 1 := max_lt hρ (by norm_num)
  have hq2 : q^2 < 1 := by nlinarith
  let N := fun n : ℕ => n+radialInnerShootingThreshold
  have hN : StrictMono N := fun _ _ hij => Nat.add_lt_add_right hij _
  have hdecay : Tendsto (fun n => 2*((N n : ℝ)*(q^2)^(N n))) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_def] using
      ((tendsto_self_mul_const_pow_of_lt_one (sq_nonneg q) hq2).comp
        hN.tendsto_atTop).const_mul 2
  filter_upwards [hN.tendsto_atTop.eventually hann,
    hdecay.eventually (gt_mem_nhds hε)] with n hn he z r hr
  let Z := radialExteriorCanonical (radialShootingNu (N n) z) (N n) (radialShootingM z)
    (Real.log innerBoundaryRadius)
  have hrp : 0 < r := lt_trans (by linarith [innerBoundaryRadius_bounds.1]) hr
  have hF : ‖(Z (Real.log r)).1‖ ≤ q :=
    (hn z (Real.log r) (Real.log_le_log
      (by linarith [innerBoundaryRadius_bounds.1]) hr.le)).2.trans (le_max_left _ _)
  rw [radialMatched_exterior_pressure n z r hr]
  calc
    _ ≤ 2*(N n : ℝ)*q^(2*N n) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hF _) (by positivity)
    _ = 2*((N n : ℝ)*(q^2)^(N n)) := by rw [pow_mul]; ring
    _ < ε := he

theorem radialMatched_global_pressure_bound :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall, ∀ r : ℝ, 0 ≤ r →
      ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold)) ≤ 1 := by
  filter_upwards [radialMatched_exterior_pressure_small 1 (by norm_num)] with n hn z r hr
  by_cases hi : r ≤ innerBoundaryRadius
  · exact ((radialMatchedAmplitude_inner_bounds n z r ⟨hr,hi⟩).2).trans (by norm_num)
  · have hrb : innerBoundaryRadius < r := lt_of_not_ge hi
    have hb := hn z r hrb
    have ha := radialShootingA_bounds n (profileMatchingParameter z)
    have hq : 0 ≤ ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold))/
        radialShootingA n := div_nonneg (by positivity) ha.1.le
    have hr2 : 1 ≤ r^2 := by nlinarith [innerBoundaryRadius_bounds.1]
    have hq1 : ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold))/
        radialShootingA n < 1 := by nlinarith
    exact ((div_lt_one ha.1).mp hq1).le.trans ha.2.le

end DefocusingNLS

end OAI
