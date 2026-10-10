import OAI.Analysis.CircleDomains.Topology.JordanIntersectionConnectivity
import Mathlib.Topology.Connected.LocallyConnected

namespace OAI

/-! Components of an open planar set cut by a disk are relatively closed,
and a component approaching an available circle point occupies its whole
small inner neighborhood. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma closure_component_inter_subset {V : Set ℂ} {x : ℂ} (hx : x ∈ V) :
    closure (connectedComponentIn V x) ∩ V ⊆ connectedComponentIn V x := by
  have hc : IsPreconnected (closure (connectedComponentIn V x) ∩ V) :=
    isPreconnected_connectedComponentIn.subset_closure
      (fun z hz => ⟨subset_closure hz, connectedComponentIn_subset V x hz⟩) inter_subset_left
  exact hc.subset_connectedComponentIn ⟨subset_closure (mem_connectedComponentIn hx), hx⟩
    inter_subset_right

lemma disk_component_boundary_neighborhood {E : Set ℂ} (hE : IsOpen E)
    {x z : ℂ} (hzE : z ∈ E)
    (hz : z ∈ closure (connectedComponentIn (E ∩ ball 0 1) x)) :
    ∃ r > 0, ball z r ∩ ball 0 1 ⊆ connectedComponentIn (E ∩ ball 0 1) x ∧
      ball z r ∩ sphere 0 1 ⊆ closure (connectedComponentIn (E ∩ ball 0 1) x) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hE z hzE
  have hS : IsPreconnected (ball z r ∩ ball (0 : ℂ) 1) :=
    ((convex_ball z r).inter (convex_ball 0 1)).isPreconnected
  obtain ⟨a, ha, haC⟩ := mem_closure_iff.1 hz (ball z r) isOpen_ball (mem_ball_self hr)
  have haV := connectedComponentIn_subset (E ∩ ball 0 1) x haC
  have hsub : ball z r ∩ ball 0 1 ⊆ E ∩ ball 0 1 := fun _ hy => ⟨hball hy.1, hy.2⟩
  have hSsub : ball z r ∩ ball 0 1 ⊆ connectedComponentIn (E ∩ ball 0 1) x := by
    have hh := hS.subset_connectedComponentIn ⟨ha, haV.2⟩ hsub
    rwa [← connectedComponentIn_eq haC] at hh
  refine ⟨r, hr, hSsub, ?_⟩
  intro y hy
  apply closure_mono hSsub
  apply isOpen_ball.inter_closure
  rw [closure_ball _ one_ne_zero]
  exact ⟨hy.1, sphere_subset_closedBall hy.2⟩

lemma disk_component_touches_available_circle {E : Set ℂ} (hE : IsOpen E)
    (hEc : IsPreconnected E) (hC : (E ∩ sphere (0 : ℂ) 1).Nonempty)
    {x : ℂ} (hx : x ∈ E ∩ ball 0 1) :
    (closure (connectedComponentIn (E ∩ ball 0 1) x) ∩ (E ∩ sphere 0 1)).Nonempty := by
  let V := E ∩ ball (0 : ℂ) 1
  let A := connectedComponentIn V x
  have hxA : x ∈ A := mem_connectedComponentIn hx
  have hAo : IsOpen A := (hE.inter isOpen_ball).connectedComponentIn
  have hAc : closure A ⊆ closedBall (0 : ℂ) 1 := by
    apply closure_minimal ((connectedComponentIn_subset V x).trans (inter_subset_right.trans ball_subset_closedBall)) isClosed_closedBall
  by_contra hempty
  have hclosed : closure A ∩ E ⊆ A := by
    intro y hy
    have hyn : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp (hAc hy.1)
    by_cases hylt : ‖y‖ < 1
    · exact closure_component_inter_subset hx ⟨hy.1, hy.2, mem_ball_zero_iff.mpr hylt⟩
    · exact (hempty ⟨y, hy.1, hy.2, mem_sphere_zero_iff_norm.mpr (le_antisymm hyn (not_lt.mp hylt))⟩).elim
  have hEA : E ⊆ A := hEc.subset_of_closure_inter_subset hAo ⟨x, hx.1, hxA⟩ hclosed
  obtain ⟨z, hzE, hzC⟩ := hC
  have hzV := connectedComponentIn_subset V x (hEA hzE)
  have hzlt : ‖z‖ < 1 := mem_ball_zero_iff.mp hzV.2
  exact (ne_of_lt hzlt) (mem_sphere_zero_iff_norm.mp hzC)

end CircleDomainRigidity

end

end OAI
