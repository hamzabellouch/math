import OAI.Analysis.CircleDomains.Topology.DiskArcIndex

namespace OAI

/-! Local constancy of the actual arc index on the punctured disk cover. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem isLocallyConstant_of_continuous_circle_zero
    {X : Type*} [TopologicalSpace X] (f : X → ℝ) (hf : Continuous f)
    (hzero : ∀ x, (f x : UnitAddCircle) = 0) : IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_eventually_eq f).mpr
  intro x
  obtain ⟨m, hm⟩ := eventually_lifts_differ_by_integer hf.continuousAt
    (continuousAt_const (y := (0 : ℝ))) (Eventually.of_forall hzero)
  have hx : f x = (m : ℝ) := by simpa only [zero_add] using hm.self_of_nhds
  simpa only [zero_add, ← hx] using hm

abbrev DiskArcIndexDomain (γ : C(PathTime, ℂ)) :=
  {p : CircleLiftCover normalizedArgument // ‖p.base‖ < 1 ∧ (γ, p.base) ∉ pathHitSet}

def diskArcIndexValue (γ : C(PathTime, ℂ)) (p : DiskArcIndexDomain γ) : ℝ :=
  diskArcIndex ⟨(γ, p.val.base), p.property.2⟩ p.val.height

theorem continuous_diskArcIndexValue (γ : C(PathTime, ℂ)) (hstart : ‖γ 0‖ = 1) :
    Continuous (diskArcIndexValue γ) := by
  have hb : Continuous (fun p : DiskArcIndexDomain γ => p.val.base) :=
    (CircleLiftCover.continuous_base normalizedArgument).comp continuous_subtype_val
  have hh : Continuous (fun p : DiskArcIndexDomain γ => p.val.height) :=
    (CircleLiftCover.continuous_height normalizedArgument).comp continuous_subtype_val
  have hi : Continuous (fun p : DiskArcIndexDomain γ =>
      diskInitialArgument (γ 0) p.val.base) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (continuousAt_diskInitialArgument hstart p.property.1).comp
      (f := fun q : DiskArcIndexDomain γ => q.val.base) hb.continuousAt
  have ha : Continuous (fun p : DiskArcIndexDomain γ =>
      (⟨(γ, p.val.base), p.property.2⟩ : AvoidingPathPoint)) :=
    (continuous_const.prodMk hb).subtype_mk _
  exact (((hh.add continuous_const).sub hi).sub
    (continuous_pathArgumentIncrement.comp ha)).sub continuous_const

theorem isLocallyConstant_diskArcIndexValue (γ : C(PathTime, ℂ))
    (hstart : ‖γ 0‖ = 1) (hend : γ 1 = 0) :
    IsLocallyConstant (diskArcIndexValue γ) := by
  apply isLocallyConstant_of_continuous_circle_zero _ (continuous_diskArcIndexValue γ hstart)
  intro p
  obtain ⟨n, hn⟩ := diskArcIndex_integer ⟨(γ, p.val.base), p.property.2⟩ p.val.height
    hstart hend p.val.height_projects
  change (diskArcIndex ⟨(γ, p.val.base), p.property.2⟩ p.val.height : UnitAddCircle) = 0
  rw [hn]
  exact (addCircle_eq_iff_exists_int 1 (n : ℝ) 0).mpr ⟨n, by simp⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
