import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPressureSlope

namespace OAI

/-! The actual inner pressure transport has the required small relative upper bound. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedInnerPressure_transport (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : r ∈ Icc 0 innerBoundaryRadius) :
    let m := n+radialInnerShootingThreshold
    let A := fun t => ‖radialMatchedProfile n z t‖
    let P := fun t => (A t)^(2*m)
    let w := radialVelocity (6-2*radialShootingA n) A
    w r*deriv (fun t => P t/radialShootingA n) r ≤ 1600*P r := by
  let m := n+radialInnerShootingThreshold
  let A := fun t => ‖radialMatchedProfile n z t‖
  let P := fun t => (A t)^(2*m)
  let w := radialVelocity (6-2*radialShootingA n) A
  change w r*deriv (fun t => P t/radialShootingA n) r ≤ 1600*P r
  by_cases hr0 : r=0
  · subst r
    rw [show w 0=0 from radialVelocity_origin _ _,zero_mul]
    exact mul_nonneg (by norm_num) (pow_nonneg (norm_nonneg _) _)
  have hrp : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
  have hmN : 0 < m := lt_of_lt_of_le (by norm_num) (radialShootingIndex_large n z)
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr hmN
  have hA := ((radialMatchedAmplitude_contDiffOn n z hX hz) r hrp).contDiffAt
    (Ioi_mem_nhds hrp)
  have hdA : HasDerivAt A (deriv A r) r := (hA.differentiableAt (by simp)).hasDerivAt
  have hAr : 0 < A r := norm_pos_iff.mpr (radialMatchedProfile_ne_zero n z hX r hr.1)
  have hArlo := (radialMatchedAmplitude_inner_bounds n z r hr).1.1
  have hc := (radialShootingInnerData n (profileMatchingParameter z)).hc
  rw [radialShootingInner_c_eq] at hc
  have hq := radialVelocityRatio_bounds (6-2*radialShootingA n) innerBoundaryRadius hc A
    (radialMatchedProfile_differentiable n z hX hz).continuous.norm
    (fun t ht => (radialMatchedAmplitude_inner_bounds n z t ht).1) r hr
  have hw0 : 0 ≤ w r := mul_nonneg hr.1 (by linarith [hq.1])
  have hw2 := (radialMatchedInnerPotential_bounds n z hX hz r hr).2
  have hwA : w r/A r ≤ 4 := by
    apply (div_le_iff₀ hAr).2
    change (w r)^2 ≤ 3 at hw2
    change (999/1000 : ℝ) ≤ A r at hArlo
    have hwu : w r ≤ 2 := by nlinarith
    linarith
  have hP0 : 0 ≤ P r := pow_nonneg hAr.le _
  have hpower : (A r)^(2*m-1)=P r/A r := by
    apply (eq_div_iff hAr.ne').2
    change (A r)^(2*m-1)*A r=(A r)^(2*m)
    rw [← pow_succ]
    congr 1
    omega
  have hdP := (hdA.pow (2*m)).div_const (radialShootingA n)
  change HasDerivAt (fun t => P t/radialShootingA n) _ r at hdP
  have hdPeq : deriv (fun t => P t/radialShootingA n) r=
      4*(m : ℝ)^2*(P r/A r)*deriv A r := by
    rw [hdP.deriv,hpower]
    simp only [radialShootingA,Nat.cast_mul,Nat.cast_ofNat]
    change ((2*(m : ℝ))*(P r/A r)*deriv A r)/(1/(2*(m : ℝ)))=_
    field_simp
    ring
  rw [hdPeq]
  have hs := radialMatchedInnerSlope_bound n z hX hz r hr
  have hcoef : 0 ≤ 4*(m : ℝ)^2*(w r/A r)*P r := by positivity
  calc
    w r*(4*(m : ℝ)^2*(P r/A r)*deriv A r)=
        (4*(m : ℝ)^2*(w r/A r)*P r)*deriv A r := by ring
    _ ≤ (4*(m : ℝ)^2*(w r/A r)*P r)*(100/(m : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hs hcoef
    _ = 400*(w r/A r)*P r := by field_simp [hm.ne']; ring
    _ ≤ 1600*P r := by nlinarith [mul_le_mul_of_nonneg_right hwA hP0]

end DefocusingNLS

end OAI
