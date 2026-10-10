import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialAmplitudeEquation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShootingInnerAverage

namespace OAI

/-! Inner pressure bounds and endpoint data for the actual matched amplitude. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedAmplitude_eq_inner (n : ℕ) (z : ProfileMatchingBall) (r : ℝ)
    (hr : r ∈ Icc 0 innerBoundaryRadius) :
    ‖radialMatchedProfile n z r‖=radialShootingInnerAmplitude n (profileMatchingParameter z) r := by
  rw [radialMatchedProfile,ite_eq_left hr.2]
  exact radialShootingInner_norm n (profileMatchingParameter z) r hr

theorem radialMatchedAmplitude_inner_bounds (n : ℕ) (z : ProfileMatchingBall)
    (r : ℝ) (hr : r ∈ Icc 0 innerBoundaryRadius) :
    ‖radialMatchedProfile n z r‖ ∈ Icc (999/1000 : ℝ) 1 ∧
      ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold)) ≤ (1/2 : ℝ) := by
  rw [radialMatchedAmplitude_eq_inner n z r hr]
  have hi := (radialShootingInnerAmplitude_spec n (profileMatchingParameter z)).2.2.2.2.1 r
    (by simpa only [radialShootingInnerData_R] using hr)
  rw [radialShootingInnerData_p] at hi
  simp only [Nat.add_sub_cancel] at hi
  refine ⟨⟨?_,hi.1.2⟩,hi.2⟩
  have hl := (radialShootingInnerData n (profileMatchingParameter z)).lo_lower
  linarith [hi.1.1]

theorem radialMatchedAmplitude_derivative_continuousOn (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) :
    ContinuousOn (deriv (fun r => ‖radialMatchedProfile n z r‖)) (Icc 0 R) := by
  have hQ : ContinuousOn (radialMatchedProfile n z) (Icc 0 R) :=
    (radialMatchedProfile_differentiable n z hX hz).continuous.continuousOn
  have hD := radialMatchedProfile_derivative_continuousOn n z hX hz R
  have hn := Complex.continuous_re.comp_continuousOn (hQ.star.mul hD)
  have hd := hn.div hQ.norm (fun r hr => norm_ne_zero_iff.mpr
    (radialMatchedProfile_ne_zero n z hX r hr.1))
  apply hd.congr
  intro r hr
  apply (eq_div_iff (norm_ne_zero_iff.mpr
    (radialMatchedProfile_ne_zero n z hX r hr.1))).2
  change deriv (fun t => ‖radialMatchedProfile n z t‖) r*‖radialMatchedProfile n z r‖=
    (star (radialMatchedProfile n z r)*deriv (radialMatchedProfile n z) r).re
  simpa only [mul_comm] using complexAmplitude_first_derivative _ r
    (radialMatchedProfile_differentiable n z hX hz r)
    (radialMatchedProfile_ne_zero n z hX r hr.1)

theorem radialMatchedAmplitude_derivative_zero (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) :
    deriv (fun r => ‖radialMatchedProfile n z r‖) 0=0 := by
  have hQ0 : deriv (radialMatchedProfile n z) 0=0 := by
    rw [radialMatchedProfile_deriv_eq_inner n z 0
      (by linarith [innerBoundaryRadius_bounds.1])]
    exact radialShootingInner_derivative_zero n (profileMatchingParameter z)
  have hh := complexAmplitude_first_derivative _ 0
    (radialMatchedProfile_differentiable n z hX hz 0)
    (radialMatchedProfile_ne_zero n z hX 0 le_rfl)
  rw [hQ0,mul_zero,Complex.zero_re] at hh
  exact (mul_eq_zero.mp hh).resolve_left (norm_ne_zero_iff.mpr
    (radialMatchedProfile_ne_zero n z hX 0 le_rfl))

theorem radialMatchedAmplitude_endpoint_derivative_nonpos (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) :
    deriv (fun r => ‖radialMatchedProfile n z r‖) innerBoundaryRadius ≤ 0 := by
  let A := fun r => ‖radialMatchedProfile n z r‖
  have hR : 0 < innerBoundaryRadius := by linarith [innerBoundaryRadius_bounds.1]
  have hmin : IsMinOn A (Icc 0 innerBoundaryRadius) innerBoundaryRadius := by
    intro r hr
    change ‖radialMatchedProfile n z innerBoundaryRadius‖ ≤ ‖radialMatchedProfile n z r‖
    rw [radialMatchedAmplitude_eq_inner n z r hr,
      radialMatchedAmplitude_eq_inner n z innerBoundaryRadius ⟨hR.le,le_rfl⟩]
    have hH := radialShootingInnerAmplitude_spec n (profileMatchingParameter z)
    have hv := hH.2.2.1
    rw [radialShootingInnerData_R] at hv
    rw [hv]
    exact (hH.2.2.2.2.1 r (by simpa only [radialShootingInnerData_R] using hr)).1.1
  have hdir : 0-innerBoundaryRadius ∈ posTangentConeAt (Icc 0 innerBoundaryRadius) innerBoundaryRadius :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc (0 : ℝ) innerBoundaryRadius).segment_subset ⟨hR.le,le_rfl⟩ ⟨le_rfl,hR.le⟩)
  have hA := (radialMatchedProfile_differentiable n z hX hz innerBoundaryRadius).norm ℂ
    (radialMatchedProfile_ne_zero n z hX innerBoundaryRadius hR.le)
  have hn : 0 ≤ deriv A innerBoundaryRadius*(0-innerBoundaryRadius) := by
    simpa only [ContinuousLinearMap.smulRight_apply,one_apply_eq_self,mul_comm] using!
      hmin.isLocalMinOn.hasFDerivWithinAt_nonneg hA.hasDerivAt.hasFDerivAt.hasFDerivWithinAt hdir
  change deriv A innerBoundaryRadius ≤ 0
  nlinarith

end DefocusingNLS

end OAI
