import OAI.Analysis.CircleDomains.Topology.RoundCollarLifts

namespace OAI

/-! Every neighborhood of one finite round hole meets the exterior of
all the holes, also when the chosen hole is a point. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_exterior_point_near_round_hole
    {I : Type*} [Fintype I] (c : I → ℂ) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (i : I) {O : Set ℂ} (hO : IsOpen O) (hiO : closedBall (c i) (r i) ⊆ O) :
    ∃ z ∈ O, z ∉ ⋃ j, closedBall (c j) (r j) := by
  obtain ⟨δ, hδ, hdδ⟩ := exists_common_round_hole_offset c r hr hd
    isOpen_univ (fun _ => subset_univ _)
  obtain ⟨η, hη, hηO⟩ := (isCompact_closedBall (c i) (r i)).exists_cthickening_subset_open hO hiO
  let ρ := min δ η / 2
  have hρ : 0 < ρ := half_pos (lt_min hδ hη)
  have hρδ : ρ ≤ δ := (half_le_self (le_of_lt (lt_min hδ hη))).trans (min_le_left _ _)
  have hρη : ρ ≤ η := (half_le_self (le_of_lt (lt_min hδ hη))).trans (min_le_right _ _)
  let z := unitCircleParam (c i) (r i + ρ) 0
  have hz : z ∈ closedBall (c i) (r i + ρ) :=
    sphere_subset_closedBall (circleMap_mem_sphere _ (by linarith [hr i]) _)
  refine ⟨z, ?_, unitCircleParam_mem_round_exterior c r hr hρ (hdδ ρ ⟨hρ, hρδ⟩).2 i 0⟩
  apply hηO
  have hzη : z ∈ closedBall (c i) (r i + η) :=
    closedBall_subset_closedBall (show r i + ρ ≤ r i + η by linarith) hz
  simpa only [cthickening_closedBall hη.le (hr i), add_comm] using hzη

end CircleDomainRigidity

end

end OAI
