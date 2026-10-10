import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialScalarBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCoefficientTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Outgoing decay makes every spectral energy boundary trace vanish. -/

open Set Filter Asymptotics
namespace DefocusingNLS
open ProfileCertificate

/-- The first two outgoing symbol estimates needed when Re λ ≥ 4. -/
def HasRadialEnergyDecay (f : ℝ → ℝ) : Prop :=
  f =O[atTop] (fun r : ℝ => r^(-8 : ℝ)) ∧
    deriv f =O[atTop] (fun r : ℝ => r^(-9 : ℝ))

theorem radialSpectralBoundary_tendsto (n : ℕ) (z : ProfileMatchingBall)
    (s t : ℝ) (q f g : ℝ → ℝ)
    (hM : radialMassDensity n z =O[atTop] (fun r : ℝ => r^(11 : ℝ)))
    (hF : radialMassFlux n z =O[atTop] (fun r : ℝ => r^(12 : ℝ)))
    (hq : q =O[atTop] (fun r : ℝ => r^(0 : ℝ)))
    (hf : HasRadialEnergyDecay f) (hg : HasRadialEnergyDecay g) :
    Tendsto (fun R => radialSpectralBoundary n z R s t q f g) atTop (nhds 0) := by
  have hff := IsBigO.mul_atTop_rpow_of_isBigO_rpow (-8) (-8) (-16) hf.1 hf.1 (by norm_num)
  have hdd := IsBigO.mul_atTop_rpow_of_isBigO_rpow (-9) (-9) (-18) hf.2 hf.2 (by norm_num)
  have hFq := IsBigO.mul_atTop_rpow_of_isBigO_rpow 12 0 12 hF hq (by norm_num)
  have hP := IsBigO.mul_atTop_rpow_of_isBigO_rpow 12 (-16) (-4) hFq hff (by norm_num)
  have hG := IsBigO.mul_atTop_rpow_of_isBigO_rpow 12 (-18) (-4) hF hdd (by norm_num)
  have hT := (hf.1.const_mul_left s).add (hg.1.const_mul_left t)
  have hMT := IsBigO.mul_atTop_rpow_of_isBigO_rpow 11 (-8) 3 hM hT (by norm_num)
  have hD := IsBigO.mul_atTop_rpow_of_isBigO_rpow 3 (-9) (-4) hMT hf.2 (by norm_num)
  have hr := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<4)
  have hz := (((hP.trans_tendsto hr).sub (hG.trans_tendsto hr)).const_mul (1/2 : ℝ)).sub
    (hD.trans_tendsto hr)
  simp only [sub_self,mul_zero] at hz
  apply hz.congr'
  filter_upwards [] with r
  simp only [Pi.mul_apply,radialSpectralBoundary]
  ring

theorem radialHardyBoundary_tendsto (a : ℝ) (f : ℝ → ℝ)
    (hH : radialHardyFlux a =O[atTop] (fun r : ℝ => r^(10 : ℝ)))
    (hf : HasRadialEnergyDecay f) :
    Tendsto (fun R => radialHardyFlux a R*(f R)^2) atTop (nhds 0) := by
  have hff := IsBigO.mul_atTop_rpow_of_isBigO_rpow (-8) (-8) (-16) hf.1 hf.1 (by norm_num)
  have hP := IsBigO.mul_atTop_rpow_of_isBigO_rpow 10 (-16) (-4) hH hff (by norm_num)
  have hh := hP.trans_tendsto
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<4))
  change Tendsto (fun R => radialHardyFlux a R*(f R*f R)) atTop (nhds 0) at hh
  simpa only [pow_two] using hh

theorem radialMatched_weight_bigO :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 →
      radialMassDensity n z =O[atTop] (fun r : ℝ => r^(11 : ℝ)) ∧
      radialMassFlux n z =O[atTop] (fun r : ℝ => r^(12 : ℝ)) ∧
      radialSpectralPressure n z =O[atTop] (fun r : ℝ => r^(0 : ℝ)) ∧
      radialHardyFlux (radialShootingA n) =O[atTop] (fun r : ℝ => r^(10 : ℝ)) := by
  filter_upwards [radialMatched_coefficient_tail] with n hn z hX hz
  have hc := hn z hX hz
  refine ⟨IsBigO.of_bound 144 ?_,IsBigO.of_bound 144 ?_,
    IsBigO.of_bound (1/radialShootingA n) ?_,IsBigO.of_bound 1 ?_⟩
  · filter_upwards [hc,eventually_gt_atTop (0 : ℝ)] with r hr hr0
    simpa only [Real.rpow_ofNat,Real.norm_eq_abs,abs_of_nonneg hr.1,
      abs_of_nonneg (pow_nonneg hr0.le 11)] using hr.2.1
  · filter_upwards [hc,eventually_gt_atTop (0 : ℝ)] with r hr hr0
    simpa only [Real.rpow_ofNat,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hr0.le 12)] using hr.2.2.1
  · filter_upwards [hc] with r hr
    simpa only [Real.rpow_zero,norm_one,mul_one,Real.norm_eq_abs,abs_of_nonneg hr.2.2.2.1]
      using hr.2.2.2.2.1
  · filter_upwards [hc,eventually_gt_atTop (0 : ℝ)] with r hr hr0
    simpa only [Real.rpow_ofNat,Real.norm_eq_abs,abs_of_nonneg hr.2.2.2.2.2.1,
      abs_of_nonneg (pow_nonneg hr0.le 10),one_mul] using hr.2.2.2.2.2.2

end DefocusingNLS

end OAI
