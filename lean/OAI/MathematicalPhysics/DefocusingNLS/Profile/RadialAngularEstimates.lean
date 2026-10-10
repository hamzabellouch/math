import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialAngularForms
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialOutgoingBoundary

namespace OAI

/-! Positive angular energy, radial monotonicity, and vanishing outgoing angular trace. -/

open Set Filter Asymptotics
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialAngularForm_mono (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (f : ℝ → ℝ) (hf : Continuous f) :
    MonotoneOn (fun R => radialAngularForm n z R f f) (Ici 0) := by
  have hK := (radialAngularDensity_continuous n z hX hz).mul (hf.pow 2)
  intro R hR S _hS hRS
  have hpos : 0 ≤ ∫ r in R..S, radialAngularDensity n z r*(f r)^2 := by
    apply intervalIntegral.integral_nonneg hRS
    intro r hr
    have hr0 := hR.trans hr.1
    unfold radialAngularDensity
    positivity
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hK.intervalIntegrable (μ := MeasureTheory.volume) 0 R)
    (hK.intervalIntegrable (μ := MeasureTheory.volume) R S)
  simp only [Pi.mul_apply,Pi.pow_apply] at he
  change radialAngularForm n z R f f ≤ radialAngularForm n z S f f
  rw [radialAngularForm_diag,radialAngularForm_diag]
  linarith

theorem radialAngularForm_coercive (n : ℕ) (z : ProfileMatchingBall)
    (R σ : ℝ) (hR : 0 ≤ R) (hσ : 4 ≤ σ) (f : ℝ → ℝ)
    (hv : ∀ r ∈ Icc 0 R, 0 ≤ radialMatchedVelocityRatio n z r) :
    (3/4 : ℝ)*radialAngularForm n z R f f ≤
      σ*radialAngularForm n z R f f+radialAngularVirial n z R f := by
  have hA := radialAngularForm_nonneg n z R hR f
  have ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
  have hV : 0 ≤ ∫ r in (0 : ℝ)..R,
      radialMatchedVelocityRatio n z r*radialAngularDensity n z r*(f r)^2 := by
    apply intervalIntegral.integral_nonneg hR
    intro r hr
    have hr0 := hr.1
    have hvr := hv r hr
    unfold radialAngularDensity
    positivity
  have hcoef : 1 ≤ σ-(6-2*radialShootingA n)/2 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcoef hA
  unfold radialAngularVirial
  nlinarith

theorem radialMatched_angular_density_bigO :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      radialAngularDensity n z =O[atTop] (fun r : ℝ => r^(9 : ℝ)) := by
  obtain ⟨d,_hd,hW⟩ := radialMatched_uniform_weight_comparison
  filter_upwards [hW] with n hn z
  refine IsBigO.of_bound 144 ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hμ := (hn z r hr.le).2
  have ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
  have hρ : radialHardyWeight (radialShootingA n) r ≤ 1 := by
    unfold radialHardyWeight
    exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg r]) (by linarith)
  have hp : ‖radialMatchedProfile n z r‖^2 ≤ 144 := by
    change ‖radialMatchedProfile n z r‖^2 ≤ 144*radialHardyWeight (radialShootingA n) r at hμ
    linarith
  have hK : 0 ≤ radialAngularDensity n z r := by
    unfold radialAngularDensity
    positivity
  simp only [Real.norm_eq_abs,Real.rpow_ofNat,abs_of_nonneg hK,
    abs_of_nonneg (pow_nonneg hr.le 9)]
  unfold radialAngularDensity
  nlinarith [mul_le_mul_of_nonneg_left hp (pow_nonneg hr.le 9)]

theorem radialAngularBoundary_tendsto (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (f : ℝ → ℝ) (hf : HasRadialEnergyDecay f)
    (hK : radialAngularDensity n z =O[atTop] (fun r : ℝ => r^(9 : ℝ))) :
    Tendsto (fun R => radialAngularBoundary n z R f) atTop (nhds 0) := by
  have hw : radialMatchedVelocity n z =O[atTop] (fun r : ℝ => r^(1 : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [radialMatchedVelocity_eventually_bound n z hX hz,
      eventually_gt_atTop (0 : ℝ)] with r hwr hr
    simpa only [Real.norm_eq_abs,Real.rpow_one,abs_of_pos hr,one_mul] using hwr
  have hKw := IsBigO.mul_atTop_rpow_of_isBigO_rpow 9 1 10 hK hw (by norm_num)
  have hff := IsBigO.mul_atTop_rpow_of_isBigO_rpow (-8) (-8) (-16) hf.1 hf.1 (by norm_num)
  have hT := IsBigO.mul_atTop_rpow_of_isBigO_rpow 10 (-16) (-4) hKw hff (by norm_num)
  have ht := (hT.trans_tendsto (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<4))).const_mul
    (1/2 : ℝ)
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [] with R
  simp only [Pi.mul_apply,radialAngularBoundary]
  ring

end DefocusingNLS

end OAI
