import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedInnerAmplitude
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureMaximum

namespace OAI

/-! Quantitative inner potential estimates for the actual matched profiles. -/

open Set
namespace DefocusingNLS
open ProfileCertificate

theorem radialShootingIndex_large (n : ℕ) (z : ProfileMatchingBall) :
    100 ≤ n+radialInnerShootingThreshold := by
  have hh := (radialShootingInnerData n (profileMatchingParameter z)).hp
  rw [radialShootingInnerData_p] at hh
  omega

theorem radialShootingC_eq (n : ℕ) (z : ProfileMatchingBall) :
    6-2*radialShootingA n=6-1/((n+radialInnerShootingThreshold : ℕ) : ℝ) :=
  (radialShootingInner_c_eq n (profileMatchingParameter z)).symm.trans
    (radialShootingInnerData_c n (profileMatchingParameter z))

theorem radialMatchedInnerPotential_bounds (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : r ∈ Icc 0 innerBoundaryRadius) :
    let A := fun t => ‖radialMatchedProfile n z t‖
    let c := 6-2*radialShootingA n
    radialAmplitudePotential c (radialShootingB (profileMatchingParameter z)) A r ∈
      Icc (3/10 : ℝ) (1/2) ∧ (radialVelocity c A r)^2 ≤ 3 := by
  let A := fun t => ‖radialMatchedProfile n z t‖
  let c := 6-2*radialShootingA n
  have hc : c ∈ Icc (599/100 : ℝ) 6 := by
    rw [show c=(radialShootingInnerData n (profileMatchingParameter z)).c from
      (radialShootingInner_c_eq n (profileMatchingParameter z)).symm]
    exact (radialShootingInnerData n (profileMatchingParameter z)).hc
  have hb := (radialShooting_geometry (profileMatchingParameter z)).1
  have hA : Continuous A := (radialMatchedProfile_differentiable n z hX hz).continuous.norm
  have hAI (t : ℝ) (ht : t ∈ Icc 0 innerBoundaryRadius) :
      A t ∈ Icc (999/1000 : ℝ) 1 := (radialMatchedAmplitude_inner_bounds n z t ht).1
  have hV := radialAmplitudePotential_bounds c _ innerBoundaryRadius hc hb
    innerBoundaryRadius_bounds.2 A hA hAI r hr
  have hq := radialVelocityRatio_bounds c innerBoundaryRadius hc A hA hAI r hr
  have hr2 : r^2 ≤ 11 := ((sq_le_sq₀ hr.1 (hr.1.trans hr.2)).2 hr.2).trans
    innerBoundaryRadius_bounds.2
  have hq2 : (radialVelocityRatio c A r)^2 ≤ (51/100 : ℝ)^2 := by nlinarith [hq.1,hq.2]
  have hw := mul_le_mul hr2 hq2 (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 11)
  refine ⟨hV,?_⟩
  change (radialVelocity c A r)^2 ≤ 3
  rw [radialVelocity,mul_pow]
  exact hw.trans (by norm_num)

theorem radialMatchedPressureRatio_bound (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : r ∈ Icc 0 innerBoundaryRadius)
    (hP : (1/5 : ℝ) ≤ ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold))) :
    radialVelocityRatio (6-2*radialShootingA n) (fun t => ‖radialMatchedProfile n z t‖) r ≤
      1/2+3/(4*((n+radialInnerShootingThreshold : ℕ) : ℝ)) := by
  let m := n+radialInnerShootingThreshold
  have hm : 0 < m := lt_of_lt_of_le (by norm_num) (radialShootingIndex_large n z)
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hc := (radialShootingInnerData n (profileMatchingParameter z)).hc
  rw [radialShootingInner_c_eq] at hc
  have hh := radialVelocityRatio_pressure_bound m hm (6-2*radialShootingA n) r
    (by linarith [hc.1]) hr.1 (fun t => ‖radialMatchedProfile n z t‖)
    (radialMatchedProfile_differentiable n z hX hz).continuous.norm
    (norm_pos_iff.mpr (radialMatchedProfile_ne_zero n z hX r hr.1))
    (fun t ht => (radialMatchedAmplitude_inner_bounds n z t ⟨ht.1,ht.2.trans hr.2⟩).2) hP
  calc
    _ ≤ (6-2*radialShootingA n)/12*(1+3/(2*(m : ℝ))) := hh
    _ ≤ 6/12*(1+3/(2*(m : ℝ))) := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hc.2 (by norm_num)) (by positivity)
    _ = 1/2+3/(4*((n+radialInnerShootingThreshold : ℕ) : ℝ)) := by
      change 6/12*(1+3/(2*(m : ℝ)))=1/2+3/(4*(m : ℝ))
      field_simp [hmR.ne']
      ring

theorem radialMatchedPressure_potential_derivative_bound (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : r ∈ Ioc 0 innerBoundaryRadius)
    (hP : (1/5 : ℝ) ≤ ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold))) :
    let m := n+radialInnerShootingThreshold
    let A := fun t => ‖radialMatchedProfile n z t‖
    let c := 6-2*radialShootingA n
    let w := radialVelocity c A
    let V := radialAmplitudePotential c (radialShootingB (profileMatchingParameter z)) A
    deriv V r ≤ 20/(m : ℝ)+(w r)^2*deriv A r/A r := by
  let m := n+radialInnerShootingThreshold
  let A := fun t => ‖radialMatchedProfile n z t‖
  let c := 6-2*radialShootingA n
  let w := radialVelocity c A
  let q := radialVelocityRatio c A r
  let V := radialAmplitudePotential c (radialShootingB (profileMatchingParameter z)) A
  change deriv V r ≤ 20/(m : ℝ)+(w r)^2*deriv A r/A r
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (le_trans (by norm_num) (radialShootingIndex_large n z))
  have hm0 : (0 : ℝ) < m := by linarith
  have hc := (radialShootingInnerData n (profileMatchingParameter z)).hc
  rw [radialShootingInner_c_eq] at hc
  have hqlo := (radialVelocityRatio_bounds c innerBoundaryRadius hc A
    (radialMatchedProfile_differentiable n z hX hz).continuous.norm
    (fun t ht => (radialMatchedAmplitude_inner_bounds n z t ht).1) r ⟨hr.1.le,hr.2⟩).1
  have hqhi := radialMatchedPressureRatio_bound n z hX hz r ⟨hr.1.le,hr.2⟩ hP
  have hqhi' : q ≤ 1/2+3*(1/(m : ℝ))/4 := by
    calc
      q ≤ 1/2+3/(4*(m : ℝ)) := hqhi
      _ = _ := by field_simp [hm0.ne']
  have ha1 : 1/(m : ℝ) ≤ 1 := (div_le_iff₀ hm0).2 (by linarith)
  have hpoly : 1/8-c/2*q+11/2*q^2 ≤ 6/(m : ℝ) := by
    rw [show c=6-1/(m : ℝ) from radialShootingC_eq n z]
    convert radial_pressure_potential_polynomial (1/(m : ℝ)) q (by positivity) ha1 hqlo hqhi' using 1
    ring
  have hwr : w r/r=q := by
    dsimp only [w,radialVelocity,q]
    field_simp [hr.1.ne']
  have hd := radialMatchedPotential_hasDerivAt n z hX hz r hr.1
  change HasDerivAt V
    (r*(1/8-c/2*(w r/r)+11/2*(w r/r)^2)+(w r)^2*deriv A r/A r) r at hd
  rw [hwr] at hd
  rw [hd.deriv]
  refine add_le_add ?_ le_rfl
  calc
    r*(1/8-c/2*q+11/2*q^2) ≤ r*(6/(m : ℝ)) := mul_le_mul_of_nonneg_left hpoly hr.1.le
    _ ≤ 20/(m : ℝ) := by
      have hR : innerBoundaryRadius ≤ (10/3 : ℝ) := by
        nlinarith [innerBoundaryRadius_bounds.1,innerBoundaryRadius_bounds.2]
      rw [← mul_div_assoc]
      apply (div_le_div_iff_of_pos_right hm0).2
      nlinarith [hr.2]

end DefocusingNLS

end OAI
