import OAI.Analysis.CircleDomains.Topology.CompactDiskRayBounds

namespace OAI

/-! A continuous lift of each actual terminal arc to angular and logarithmic
coordinates. The angular origin is the representative of the arc start. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

abbrev DiskRayTime := {t : PathTime // t < ⊤}

def diskRayAngle (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0)
    (t : DiskRayTime) : ℝ :=
  realCirclePathLift (initialArcAngles puncturedArgument γ hi he t.val t.property) 1

theorem diskRayAngle_eq_increment (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0)
    (t : DiskRayTime) :
    diskRayAngle γ hi he t = circleRepresentative (normalizedArgument (γ 0)) +
      circlePathIncrement (initialArcAngles puncturedArgument γ hi he t.val t.property) := by
  have h0 : realCirclePathLift (initialArcAngles puncturedArgument γ hi he t.val t.property) 0 =
      circleRepresentative (normalizedArgument (γ 0)) := by
    rw [realCirclePathLift, (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath_zero]
    simp only [initialArcAngles, ContinuousMap.coe_mk, zero_mul, puncturedArgument]
  unfold diskRayAngle circlePathIncrement
  rw [h0]
  ring

theorem continuous_diskRayAngle (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0) :
    Continuous (diskRayAngle γ hi he) := by
  let A : DiskRayTime → C(unitInterval, UnitAddCircle) := fun t =>
    initialArcAngles puncturedArgument γ hi he t.val t.property
  have hA : Continuous A := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply puncturedArgument.continuous.comp
    apply Continuous.subtype_mk
    exact γ.continuous.comp (continuous_snd.mul (continuous_subtype_val.comp continuous_fst))
  have hc := (continuous_const (y := circleRepresentative (normalizedArgument (γ 0)))).add
    (continuous_circlePathIncrement.comp hA)
  exact hc.congr (fun t => (diskRayAngle_eq_increment γ hi he t).symm)

theorem diskRayAngle_projects (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0)
    (t : DiskRayTime) :
    (diskRayAngle γ hi he t : UnitAddCircle) = normalizedArgument (γ t.val) := by
  simpa only [diskRayAngle, initialArcAngles, puncturedArgument, ContinuousMap.coe_mk, one_mul] using
    realCirclePathLift_projects (initialArcAngles puncturedArgument γ hi he t.val t.property) 1

theorem diskRayAngle_mul_prefix (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0)
    (c : DiskRayTime) (u : unitInterval) :
    diskRayAngle γ hi he ⟨u * c.val, (unitInterval.mul_le_right.trans_lt c.property)⟩ =
      realCirclePathLift (initialArcAngles puncturedArgument γ hi he c.val c.property) u := by
  let A := initialArcAngles puncturedArgument γ hi he c.val c.property
  have hp : initialArcAngles puncturedArgument γ hi he (u * c.val)
      (unitInterval.mul_le_right.trans_lt c.property) = circlePathPrefix A u := by
    ext s
    change normalizedArgument (γ (s * (u * c.val))) = normalizedArgument (γ ((s * u) * c.val))
    rw [mul_assoc]
  rw [diskRayAngle_eq_increment, hp, circlePathIncrement_prefix]
  have h0 : realCirclePathLift A 0 = circleRepresentative (normalizedArgument (γ 0)) := by
    rw [realCirclePathLift, (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath_zero]
    simp only [A, initialArcAngles, puncturedArgument, ContinuousMap.coe_mk, zero_mul]
  rw [h0]
  ring

theorem diskRay_nonzero (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0)
    (t : DiskRayTime) : γ t.val ≠ 0 := by
  intro h
  have ht := hi (h.trans he.symm)
  exact (ne_of_lt t.property) ht

def diskRayDepth (γ : C(PathTime, ℂ)) (t : DiskRayTime) : ℝ := -Real.log ‖γ t.val‖

theorem continuous_diskRayDepth (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0) :
    Continuous (diskRayDepth γ) :=
  ((γ.continuous.comp continuous_subtype_val).norm.log
    (fun t => norm_ne_zero_iff.mpr (diskRay_nonzero γ hi he t))).neg

def diskRayLift (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0) :
    C(DiskRayTime, ℝ × ℝ) :=
  ⟨fun t => (diskRayAngle γ hi he t, diskRayDepth γ t),
    (continuous_diskRayAngle γ hi he).prodMk (continuous_diskRayDepth γ hi he)⟩

theorem diskRayLift_injective (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0) :
    Injective (diskRayLift γ hi he) := by
  intro s t h
  apply Subtype.ext
  apply hi
  apply Complex.ext_norm_arg
  · have hd : Real.log ‖γ s.val‖ = Real.log ‖γ t.val‖ :=
      neg_injective (congrArg Prod.snd h)
    have hexp := congrArg Real.exp hd
    simpa only [Real.exp_log (norm_pos_iff.mpr (diskRay_nonzero γ hi he s)),
      Real.exp_log (norm_pos_iff.mpr (diskRay_nonzero γ hi he t))] using hexp
  · apply Complex.arg_coe_angle_eq_iff.mp
    apply (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).injective
    exact (diskRayAngle_projects γ hi he s).symm.trans
      ((congrArg (fun x : ℝ => (x : UnitAddCircle)) (congrArg Prod.fst h)).trans
        (diskRayAngle_projects γ hi he t))

end CircleDomainRigidity

end

end OAI
