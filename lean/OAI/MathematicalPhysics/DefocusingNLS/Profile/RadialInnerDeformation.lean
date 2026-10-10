import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPressureSlope
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformTailDeformation
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace OAI

/-! Direct positive deformation in the inner ball from the proved slope estimate. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialVelocity_hasDerivAt_zero (c : ℝ) (A : ℝ → ℝ)
    (hA : Continuous A) (hn : A 0 ≠ 0) :
    HasDerivAt (radialVelocity c A) (c/12) 0 := by
  have hq : ContinuousAt (radialVelocityRatio c A) 0 :=
    (continuous_const.mul (continuous_radialAverage (fun r => (A r)^2) (hA.pow 2))).continuousAt.div
      (hA.pow 2).continuousAt (pow_ne_zero 2 hn)
  have hq0 : radialVelocityRatio c A 0=c/12 := by
    unfold radialVelocityRatio
    rw [radialAverage_zero]
    field_simp [hn]
  apply hasDerivAt_iff_tendsto_slope.mpr
  rw [← hq0]
  apply (hq.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : r ≠ 0 := hr
  simp only [slope,radialVelocity,smul_eq_mul,vsub_eq_sub,zero_mul,sub_zero]
  field_simp [hr0]

theorem radialMatched_inner_deformation (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : r ∈ Icc 0 innerBoundaryRadius) :
    (3/10 : ℝ) ≤ deriv (radialMatchedVelocity n z) r ∧
      (3/10 : ℝ) ≤ radialVelocityRatio (6-2*radialShootingA n)
        (fun t => ‖radialMatchedProfile n z t‖) r := by
  let A := fun t => ‖radialMatchedProfile n z t‖
  let c := 6-2*radialShootingA n
  let w := radialVelocity c A
  have hc : c ∈ Icc (599/100 : ℝ) 6 := by
    rw [show c=(radialShootingInnerData n (profileMatchingParameter z)).c from
      (radialShootingInner_c_eq n (profileMatchingParameter z)).symm]
    exact (radialShootingInnerData n (profileMatchingParameter z)).hc
  have hA : Continuous A := (radialMatchedProfile_differentiable n z hX hz).continuous.norm
  have hAI (t : ℝ) (ht : t ∈ Icc 0 innerBoundaryRadius) :
      A t ∈ Icc (999/1000 : ℝ) 1 := (radialMatchedAmplitude_inner_bounds n z t ht).1
  have hq := radialVelocityRatio_bounds c innerBoundaryRadius hc A hA hAI r hr
  refine ⟨?_,by linarith [hq.1]⟩
  change (3/10 : ℝ) ≤ deriv w r
  by_cases hr0 : r=0
  · subst r
    have hn : A 0 ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (hAI 0 hr).1)
    rw [(radialVelocity_hasDerivAt_zero c A hA hn).deriv]
    linarith [hc.1]
  · have hrp : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
    have hw0 : 0 ≤ w r := mul_nonneg hr.1 (le_trans (by norm_num) hq.1)
    have hw2 := (radialMatchedInnerPotential_bounds n z hX hz r hr).2
    have hwle : w r ≤ 2 := by change (w r)^2 ≤ 3 at hw2; nlinarith
    have hAr := hAI r hr
    have hAp : 0 < A r := lt_of_lt_of_le (by norm_num) hAr.1
    have hd := radialMatchedInnerSlope_bound n z hX hz r hr
    have hm : (100 : ℝ) ≤ ((n+radialInnerShootingThreshold : ℕ) : ℝ) := by
      exact_mod_cast radialShootingIndex_large n z
    have hdsmall : deriv A r ≤ (1/100 : ℝ) := by
      have hm2 : (10000 : ℝ) ≤ ((n+radialInnerShootingThreshold : ℕ) : ℝ)^2 := by nlinarith
      have hh : 100/((n+radialInnerShootingThreshold : ℕ) : ℝ)^2 ≤ (1/100 : ℝ) :=
        (div_le_iff₀ (by positivity)).mpr (by nlinarith)
      exact hd.trans hh
    have hterm : 2*w r*deriv A r/A r ≤ (1/20 : ℝ) := by
      apply (div_le_iff₀ hAp).mpr
      have hh := mul_le_mul_of_nonneg_left hdsmall
        (show 0 ≤ (2 : ℝ)*w r from mul_nonneg (by norm_num) hw0)
      nlinarith [hAr.1]
    have hdw := radialMatchedVelocity_hasDerivAt n z hX hz r hrp
    rw [hdw.deriv]
    have he : 11/r*w r=11*radialVelocityRatio c A r := by
      dsimp only [w,radialVelocity]
      field_simp [hr0]
    rw [he]
    linarith [hc.1,hq.2]

end DefocusingNLS

end OAI
