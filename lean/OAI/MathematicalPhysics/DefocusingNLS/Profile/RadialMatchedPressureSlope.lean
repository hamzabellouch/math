import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPressureBounds

namespace OAI

/-! The positive part of the actual inner amplitude slope is O(m⁻²). -/

open Set Filter
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedInnerSlope_bound (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : r ∈ Icc 0 innerBoundaryRadius) :
    deriv (fun t => ‖radialMatchedProfile n z t‖) r ≤
      100/(((n+radialInnerShootingThreshold : ℕ) : ℝ)^2) := by
  let m := n+radialInnerShootingThreshold
  let A := fun t => ‖radialMatchedProfile n z t‖
  let c := 6-2*radialShootingA n
  let w := radialVelocity c A
  let V := radialAmplitudePotential c (radialShootingB (profileMatchingParameter z)) A
  have hm : (40 : ℝ) ≤ m := by
    exact_mod_cast (le_trans (by norm_num) (radialShootingIndex_large n z))
  by_cases hdr : deriv A r ≤ 0
  · exact hdr.trans (div_nonneg (by norm_num) (sq_nonneg _))
  have hR : 0 < innerBoundaryRadius := by linarith [innerBoundaryRadius_bounds.1]
  obtain ⟨x,hx,hdx,hmax,hzero,hthird⟩ := radial_positive_slope_maximum A innerBoundaryRadius hR
    (radialMatchedAmplitude_derivative_continuousOn n z hX hz innerBoundaryRadius)
    (le_of_eq (radialMatchedAmplitude_derivative_zero n z hX hz))
    (radialMatchedAmplitude_endpoint_derivative_nonpos n z hX hz) r hr (lt_of_not_ge hdr)
  have hxI : x ∈ Icc 0 innerBoundaryRadius := ⟨hx.1.le,hx.2.le⟩
  have hAx : 0 < A x := norm_pos_iff.mpr (radialMatchedProfile_ne_zero n z hX x hx.1.le)
  have hAx1 : A x ≤ 1 := (radialMatchedAmplitude_inner_bounds n z x hxI).1.2
  have hVbounds := radialMatchedInnerPotential_bounds n z hX hz x hxI
  have hstat := radialMatchedAmplitude_stationary n z hX hz x hx.1
  change -deriv (deriv A) x-11/x*deriv A x+(A x)^(2*m)*A x=V x*A x at hstat
  rw [hzero] at hstat
  have hdrift : 0 ≤ 11/x*deriv A x := mul_nonneg (div_nonneg (by norm_num) hx.1.le) hdx.le
  have hP : (1/5 : ℝ) ≤ (A x)^(2*m) := by
    have hvlow := mul_le_mul_of_nonneg_right hVbounds.1.1 hAx.le
    apply le_of_not_gt
    intro hp
    have hpA := mul_lt_mul_of_pos_right hp hAx
    linarith
  have hs := ((radialMatchedAmplitude_contDiffOn n z hX hz) x hx.1).contDiffAt
    (Ioi_mem_nhds hx.1)
  have hs1 := hs.derivWithin (m := ∞) (by simp)
  have hs2 := hs1.derivWithin (m := 1) (by simp)
  have hA : HasDerivAt A (deriv A x) x := (hs.differentiableAt (by simp)).hasDerivAt
  have hD : HasDerivAt (deriv A) 0 x := by
    have hh : HasDerivAt (deriv A) (deriv (deriv A) x) x :=
      (hs1.differentiableAt (by simp)).hasDerivAt
    rwa [hzero] at hh
  have hDD : HasDerivAt (deriv (deriv A)) (deriv (deriv (deriv A)) x) x :=
    (hs2.differentiableAt (by simp)).hasDerivAt
  have hV : HasDerivAt V (deriv V x) x :=
    (radialMatchedPotential_hasDerivAt n z hX hz x hx.1).differentiableAt.hasDerivAt
  have hEq : (fun t => -deriv (deriv A) t-11/t*deriv A t+(A t)^(2*m+1))
      =ᶠ[nhds x] (fun t => V t*A t) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
    have he := radialMatchedAmplitude_stationary n z hX hz t ht.1
    change -deriv (deriv A) t-11/t*deriv A t+(A t)^(2*m)*A t=V t*A t at he
    simpa only [pow_add,pow_one] using he
  have hmrel := radial_amplitude_slope_max_relation m A V x (deriv A x)
    (deriv (deriv (deriv A)) x) (deriv V x) hx.1.ne' hAx.le hdx.le hthird hA hD hDD hV hEq
  have hvder := radialMatchedPressure_potential_derivative_bound n z hX hz x
    ⟨hx.1,hx.2.le⟩ hP
  have hVsum : V x+(w x)^2 ≤ 4 := by linarith [hVbounds.1.2,hVbounds.2]
  have hbound := radial_pressure_slope_bound (m : ℝ) hm (A x) (deriv A x)
    ((A x)^(2*m)) (V x) (w x) (deriv V x) hAx hAx1 hdx.le hP hVsum hmrel hvder
  exact (hmax r hr).trans hbound

end DefocusingNLS

end OAI
