import OAI.Analysis.CircleDomains.Topology.DiskComponentBoundary

namespace OAI

/-! A connected open plane set whose available unit-circle part is
connected has connected intersection with the open unit disk. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma disk_component_closure_contains_circle {E : Set ℂ} (hE : IsOpen E)
    (hEc : IsPreconnected E) (hC : IsPreconnected (E ∩ sphere (0 : ℂ) 1))
    (hCn : (E ∩ sphere (0 : ℂ) 1).Nonempty)
    {x : ℂ} (hx : x ∈ E ∩ ball 0 1) :
    E ∩ sphere 0 1 ⊆ closure (connectedComponentIn (E ∩ ball 0 1) x) := by
  let C := E ∩ sphere (0 : ℂ) 1
  let A := connectedComponentIn (E ∩ ball (0 : ℂ) 1) x
  let : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp hC
  let T : Set C := {z | z.val ∈ closure A}
  have hTc : IsClosed T := isClosed_closure.preimage continuous_subtype_val
  have hTo : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨r, hr, _, hclose⟩ := disk_component_boundary_neighborhood hE z.property.1 hz
    have hn : ∀ᶠ w : C in 𝓝 z, w.val ∈ ball z.val r :=
      continuous_subtype_val.continuousAt.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))
    filter_upwards [hn] with w hw
    exact hclose ⟨hw, w.property.2⟩
  have hTn : T.Nonempty := by
    obtain ⟨z, hzA, hzC⟩ := disk_component_touches_available_circle hE hEc hCn hx
    exact ⟨⟨z,hzC⟩,hzA⟩
  have hTu := (show IsClopen T from ⟨hTc,hTo⟩).eq_univ hTn
  intro z hz
  have hh : (⟨z,hz⟩ : C) ∈ T := hTu.symm ▸ mem_univ _
  exact hh

lemma isPreconnected_inter_disk_of_circle {E : Set ℂ} (hE : IsOpen E)
    (hEc : IsPreconnected E) (hC : IsPreconnected (E ∩ sphere (0 : ℂ) 1)) :
    IsPreconnected (E ∩ ball 0 1) := by
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  by_cases hCn : (E ∩ sphere (0 : ℂ) 1).Nonempty
  · let V := E ∩ ball (0 : ℂ) 1
    let A := connectedComponentIn V x
    have hCA := disk_component_closure_contains_circle hE hEc hC hCn hx
    have hCB := disk_component_closure_contains_circle hE hEc hC hCn hy
    obtain ⟨z, hz⟩ := hCn
    obtain ⟨r, hr, hsub, _⟩ := disk_component_boundary_neighborhood hE hz.1 (hCA hz)
    obtain ⟨b, hb, hbB⟩ := mem_closure_iff.1 (hCB hz) (ball z r) isOpen_ball (mem_ball_self hr)
    have hbV := connectedComponentIn_subset V y hbB
    have hbA : b ∈ A := hsub ⟨hb,hbV.2⟩
    have heq : connectedComponentIn V y = A :=
      (connectedComponentIn_eq hbB).trans (connectedComponentIn_eq hbA).symm
    refine ⟨A, connectedComponentIn_subset V x, mem_connectedComponentIn hx, ?_,
      isPreconnected_connectedComponentIn⟩
    rw [← heq]
    exact mem_connectedComponentIn hy
  · have hball : E ⊆ ball (0 : ℂ) 1 := by
      apply hEc.subset_of_closure_inter_subset isOpen_ball ⟨x,hx.1,hx.2⟩
      intro z hz
      rw [closure_ball _ one_ne_zero] at hz
      have hzn : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz.1
      have hne : ‖z‖ ≠ 1 := fun he => hCn ⟨z,hz.2,mem_sphere_zero_iff_norm.mpr he⟩
      exact mem_ball_zero_iff.mpr (lt_of_le_of_ne hzn hne)
    exact ⟨E, fun z hz => ⟨hz,hball hz⟩, hx.1, hy.1,hEc⟩

end CircleDomainRigidity

end

end OAI
