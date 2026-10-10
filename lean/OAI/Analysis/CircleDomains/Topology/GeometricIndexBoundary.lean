import OAI.Analysis.CircleDomains.Selection.GeometricRayIndex

namespace OAI

/-! Calibration of the greatest-translate index on the real boundary.
The value is the floor of the horizontal coordinate minus the arc start. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem diskRayAngle_zero (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0) :
    diskRayAngle γ hi he ⟨0, bot_lt_top⟩ = circleRepresentative (normalizedArgument (γ 0)) := by
  have h := diskRayAngle_mul_prefix γ hi he (⟨0, bot_lt_top⟩ : DiskRayTime) 0
  simpa only [zero_mul, realCirclePathLift,
    (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath_zero,
    initialArcAngles, ContinuousMap.coe_mk, puncturedArgument] using h

theorem HalfPlaneRay.boundary_hit_iff (R : HalfPlaneRay) (x : ℝ) :
    halfPlaneDisk x ∈ range R.crosscut ↔ x = (R.curve ⟨0, bot_lt_top⟩).re := by
  constructor
  · rintro ⟨t, ht⟩
    have htlt : t < ⊤ := by
      by_contra hn
      have he : t = ⊤ := top_le_iff.mp (not_lt.mp hn)
      subst t
      change R.compactify ⊤ = halfPlaneDisk x at ht
      rw [R.compactify_top] at ht
      exact cayleyBoundary_ne_one x ht.symm
    change R.compactify t = halfPlaneDisk x at ht
    rw [HalfPlaneRay.compactify, dite_eq_left htlt] at ht
    have hc := halfPlaneDisk_injOn (R.nonneg ⟨t, htlt⟩) (by simp) ht
    have hzero : t = 0 := by
      by_contra hn
      have hp := R.positive ⟨t, htlt⟩ (lt_of_le_of_ne bot_le (Ne.symm hn))
      have hi := congrArg Complex.im hc
      simp only [Complex.ofReal_im] at hi
      exact (ne_of_gt hp) hi
    subst t
    exact (congrArg Complex.re hc).symm
  · intro hx
    refine ⟨0, ?_⟩
    change R.compactify 0 = halfPlaneDisk x
    rw [R.start_eq_real, hx]

theorem rayRightIndices_boundary_iff (hsch : PlanarSchoenflies)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (x : ℝ)
    (hx : ∀ k : ℤ, x ≠ circleRepresentative (normalizedArgument (γ 0)) + (k : ℝ)) (k : ℤ) :
    k ∈ rayRightIndices hsch γ hγ (x : ℂ) ↔
      (k : ℝ) < x - circleRepresentative (normalizedArgument (γ 0)) := by
  let R := translatedHalfPlaneRay γ hγ k
  have hstart : (R.curve ⟨0, bot_lt_top⟩).re =
      circleRepresentative (normalizedArgument (γ 0)) + (k : ℝ) := by
    simp only [R, translatedHalfPlaneRay, ContinuousMap.coe_mk, Complex.add_re, Complex.intCast_re]
    simp only [diskRayComplex, ContinuousMap.coe_mk, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero, diskRayAngle_zero]
  have hmiss : halfPlaneDisk x ∉ range R.crosscut := by
    rw [R.boundary_hit_iff, hstart]
    exact hx k
  have hb := R.side_boundary (rayJordan_spec hsch γ hγ k) x hmiss
  change (if halfPlaneDisk x ∈ closure (jordanInterior (rayJordan hsch γ hγ k)) then false else true) = _ at hb
  rw [hstart] at hb
  by_cases hc : halfPlaneDisk x ∈ closure (jordanInterior (rayJordan hsch γ hγ k))
  · have hle : x ≤ circleRepresentative (normalizedArgument (γ 0)) + (k : ℝ) := by
      by_contra hn
      simp only [ite_eq_left hc, ite_eq_right hn] at hb
      cases hb
    exact iff_of_false (fun h => h hc) (by linarith)
  · have hlt : circleRepresentative (normalizedArgument (γ 0)) + (k : ℝ) < x := by
      by_contra hn
      have hle := le_of_not_gt hn
      simp only [ite_eq_right hc, ite_eq_left hle] at hb
      cases hb
    exact iff_of_true hc (by linarith)

theorem geometricRayIndex_boundary_floor (hsch : PlanarSchoenflies)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (x : ℝ)
    (hx : ∀ k : ℤ, x ≠ circleRepresentative (normalizedArgument (γ 0)) + (k : ℝ)) :
    geometricRayIndex hsch γ hγ (x : ℂ) =
      ⌊x - circleRepresentative (normalizedArgument (γ 0))⌋ := by
  let a := circleRepresentative (normalizedArgument (γ 0))
  have hfloor : (⌊x - a⌋ : ℝ) < x - a := by
    apply lt_of_le_of_ne (Int.floor_le _)
    intro he
    exact hx ⌊x - a⌋ (by linarith)
  have hmem : ⌊x - a⌋ ∈ rayRightIndices hsch γ hγ (x : ℂ) :=
    (rayRightIndices_boundary_iff hsch γ hγ x hx _).mpr hfloor
  have hJ := geometricRayIndex_isGreatest hsch γ hγ (x : ℂ) (by simp)
  apply le_antisymm
  · apply Int.le_floor.mpr
    exact ((rayRightIndices_boundary_iff hsch γ hγ x hx _).mp hJ.1).le
  · exact hJ.2 hmem

end CircleDomainRigidity

end

end OAI
