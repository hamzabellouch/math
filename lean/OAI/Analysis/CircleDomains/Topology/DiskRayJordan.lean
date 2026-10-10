import OAI.Analysis.CircleDomains.Topology.DiskRayCrosscut
import OAI.Analysis.CircleDomains.Topology.BoundaryClosingArc
import OAI.Analysis.CircleDomains.Sobolev.SmoothJordanNeighborhoods

namespace OAI

/-! The actual compactified lifted ray bounds a Jordan disk after closing
along the positive boundary arc. Its entire filling stays in the unit disk. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

def diskRayCrosscut (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) :
    Path (compactifiedDiskRay γ hγ.1 hγ.2.2.1 ⊥) 1 where
  toFun := compactifiedDiskRay γ hγ.1 hγ.2.2.1
  continuous_toFun := continuous_compactifiedDiskRay hγ
  source' := rfl
  target' := compactifiedDiskRay_top γ hγ.1 hγ.2.2.1

def diskRayLoop (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) :
    Path (compactifiedDiskRay γ hγ.1 hγ.2.2.1 ⊥)
      (compactifiedDiskRay γ hγ.1 hγ.2.2.1 ⊥) :=
  (diskRayCrosscut γ hγ).trans (boundaryClosingArc _ (compactifiedDiskRay_start_norm hγ))

theorem diskRayLoop_injective_before_end (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) :
    ∀ s t : PathTime, s < 1 → t < 1 → diskRayLoop γ hγ s = diskRayLoop γ hγ t → s = t := by
  exact two_arc_loop_injective_before_end _ _ (compactifiedDiskRay_injective hγ)
    (boundaryClosingArc_injective (compactifiedDiskRay_start_norm hγ)
      (compactifiedDiskRay_start_ne_one hγ))
    (crosscut_boundary_intersections _ (compactifiedDiskRay_interior hγ)
      (compactifiedDiskRay_start_norm hγ) (compactifiedDiskRay_start_ne_one hγ))

theorem exists_diskRayJordan (hsch : PlanarSchoenflies) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) :
    ∃ H : ℂ ≃ₜ ℂ,
      frontier (jordanInterior H) = range (diskRayCrosscut γ hγ) ∪
        range (boundaryClosingArc _ (compactifiedDiskRay_start_norm hγ)) := by
  obtain ⟨H, hH⟩ := exists_schoenflies_of_simple_closed_path hsch
    (diskRayLoop γ hγ) (diskRayLoop_injective_before_end γ hγ)
  refine ⟨H, ?_⟩
  rw [frontier_jordanInterior_eq_circle_range H _ hH]
  have hr : range (fun z : Circle => circleOfClosedPath (diskRayLoop γ hγ)
      ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z)) =
      range (circleOfClosedPath (diskRayLoop γ hγ)) := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact mem_range_self _
    · rintro ⟨w, rfl⟩
      exact ⟨(AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero) w, by simp⟩
  rw [hr, circleOfClosedPath_range]
  exact Path.trans_range _ _

theorem diskRayCrosscut_norm_le (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    (t : PathTime) : ‖diskRayCrosscut γ hγ t‖ ≤ 1 := by
  by_cases ht0 : t = 0
  · rw [ht0, (diskRayCrosscut γ hγ).source]
    exact (compactifiedDiskRay_start_norm hγ).le
  by_cases ht1 : t = 1
  · rw [ht1, (diskRayCrosscut γ hγ).target, norm_one]
  exact (compactifiedDiskRay_interior hγ t
    ⟨lt_of_le_of_ne bot_le (Ne.symm ht0), lt_of_le_of_ne le_top ht1⟩).le

theorem jordan_fill_subset_closed_unitDisk (H : ℂ ≃ₜ ℂ)
    (hf : ∀ z ∈ frontier (jordanInterior H), ‖z‖ ≤ 1) :
    closure (jordanInterior H) ⊆ Metric.closedBall (0 : ℂ) 1 := by
  apply closed_jordanInterior_subset_of_unbounded_connected_compl H
  · simpa only [jordanInterior, Homeomorph.refl_apply, image_id,
      closure_ball _ one_ne_zero]
      using (isConnected_exterior_jordanInterior (Homeomorph.refl ℂ)).isPreconnected
  · intro hb
    apply NormedSpace.unbounded_univ ℝ ℂ
    have h := (isCompact_closedBall (0 : ℂ) 1).isBounded.union hb
    simpa only [union_compl_self] using h
  · intro z hz
    exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hf z hz)

theorem diskRayJordan_filling_subset (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    (H : ℂ ≃ₜ ℂ)
    (hf : frontier (jordanInterior H) = range (diskRayCrosscut γ hγ) ∪
      range (boundaryClosingArc _ (compactifiedDiskRay_start_norm hγ))) :
    closure (jordanInterior H) ⊆ Metric.closedBall (0 : ℂ) 1 ∧
      jordanInterior H ⊆ Metric.ball (0 : ℂ) 1 := by
  have hcl : closure (jordanInterior H) ⊆ Metric.closedBall (0 : ℂ) 1 := by
    apply jordan_fill_subset_closed_unitDisk
    intro z hz
    rw [hf] at hz
    rcases hz with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact diskRayCrosscut_norm_le γ hγ t
    · exact (boundaryClosingArc_norm _ _ t).le
  refine ⟨hcl, ?_⟩
  have hi := interior_mono hcl
  rw [interior_closure_jordanInterior, interior_closedBall _ one_ne_zero] at hi
  exact hi

end CircleDomainRigidity

end

end OAI
