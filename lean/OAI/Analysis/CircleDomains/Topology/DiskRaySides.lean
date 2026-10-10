import OAI.Analysis.CircleDomains.Topology.DiskRayJordan
import OAI.Analysis.CircleDomains.Topology.CrosscutSeparationInput

namespace OAI

/-! The Jordan filling is one of the two actual crosscut components.
Consequently its exterior inside the disk is connected as well. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem diskRayJordan_subset_complement (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (H : ℂ ≃ₜ ℂ)
    (hf : frontier (jordanInterior H) = range (diskRayCrosscut γ hγ) ∪
      range (boundaryClosingArc _ (compactifiedDiskRay_start_norm hγ))) :
    jordanInterior H ⊆ Metric.ball 0 1 \ range (diskRayCrosscut γ hγ) := by
  intro z hz
  refine ⟨(diskRayJordan_filling_subset γ hγ H hf).2 hz, ?_⟩
  intro hp
  have hfront : z ∈ frontier (jordanInterior H) := hf ▸ Or.inl hp
  have hi : z ∈ interior (jordanInterior H) := by
    simpa only [(jordanInterior_isOpen H).interior_eq] using hz
  exact Set.disjoint_left.mp disjoint_interior_frontier hi hfront

theorem diskRay_component_in_or_out (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (H : ℂ ≃ₜ ℂ)
    (hf : frontier (jordanInterior H) = range (diskRayCrosscut γ hγ) ∪
      range (boundaryClosingArc _ (compactifiedDiskRay_start_norm hγ)))
    {V : Set ℂ} (hV : IsPreconnected V)
    (hsub : V ⊆ Metric.ball 0 1 \ range (diskRayCrosscut γ hγ)) :
    V ⊆ jordanInterior H ∨ V ⊆ (closure (jordanInterior H))ᶜ := by
  apply hV.subset_or_subset (jordanInterior_isOpen H) isClosed_closure.isOpen_compl
  · exact disjoint_compl_right.mono_left subset_closure
  · intro z hz
    by_cases hin : z ∈ jordanInterior H
    · exact Or.inl hin
    · right
      intro hcl
      have hfront : z ∈ frontier (jordanInterior H) := by
        rw [(jordanInterior_isOpen H).frontier_eq]
        exact ⟨hcl, hin⟩
      rw [hf] at hfront
      rcases hfront with hp | ⟨t, rfl⟩
      · exact (hsub hz).2 hp
      · have hn : ‖boundaryClosingArc _ (compactifiedDiskRay_start_norm hγ) t‖ < 1 := by
          simpa only [Metric.mem_ball, dist_zero_right] using (hsub hz).1
        rw [boundaryClosingArc_norm] at hn
        exact lt_irrefl _ hn

theorem diskRay_exterior_connected (hsep : UnitDiskCrosscutSeparation)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (H : ℂ ≃ₜ ℂ)
    (hf : frontier (jordanInterior H) = range (diskRayCrosscut γ hγ) ∪
      range (boundaryClosingArc _ (compactifiedDiskRay_start_norm hγ))) :
    IsConnected (Metric.ball 0 1 \ closure (jordanInterior H)) := by
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hd, hcover, _, _⟩ :=
    hsep (diskRayCrosscut γ hγ).toContinuousMap (compactifiedDiskRay_injective hγ)
      (compactifiedDiskRay_start_norm hγ) (by simp)
      (compactifiedDiskRay_interior hγ)
  have hJsub := diskRayJordan_subset_complement γ hγ H hf
  have hJUorV : jordanInterior H ⊆ U ∨ jordanInterior H ⊆ V := by
    apply (isConnected_jordanInterior H).isPreconnected.subset_or_subset hUo hVo hd
    exact fun z hz => hcover ▸ hJsub hz
  have hcase (A B : Set ℂ) (hAc : IsConnected A) (hBc : IsConnected B)
      (hAB : Disjoint A B) (hc : A ∪ B = Metric.ball 0 1 \ range (diskRayCrosscut γ hγ))
      (hJA : jordanInterior H ⊆ A) :
      Metric.ball 0 1 \ closure (jordanInterior H) = B := by
    have hAsub : A ⊆ Metric.ball 0 1 \ range (diskRayCrosscut γ hγ) := hc ▸ subset_union_left
    have hBsub : B ⊆ Metric.ball 0 1 \ range (diskRayCrosscut γ hγ) := hc ▸ subset_union_right
    have hAJ : A ⊆ jordanInterior H := by
      rcases diskRay_component_in_or_out γ hγ H hf hAc.isPreconnected hAsub with h | h
      · exact h
      · obtain ⟨z, hz⟩ := (isConnected_jordanInterior H).nonempty
        exact (h (hJA hz) (subset_closure hz)).elim
    have hBout : B ⊆ (closure (jordanInterior H))ᶜ := by
      rcases diskRay_component_in_or_out γ hγ H hf hBc.isPreconnected hBsub with h | h
      · obtain ⟨z, hz⟩ := hBc.nonempty
        exact (Set.disjoint_left.mp hAB (hJA (h hz)) hz).elim
      · exact h
    apply Subset.antisymm
    · intro z hz
      have hn : z ∉ range (diskRayCrosscut γ hγ) := by
        intro hp
        exact hz.2 (frontier_subset_closure (hf ▸ Or.inl hp))
      have hu : z ∈ A ∪ B := hc ▸ ⟨hz.1, hn⟩
      rcases hu with hA | hB
      · exact (hz.2 (subset_closure (hAJ hA))).elim
      · exact hB
    · intro z hz
      exact ⟨(hBsub hz).1, hBout hz⟩
  rcases hJUorV with h | h
  · rw [hcase U V hUc hVc hd hcover h]
    exact hVc
  · rw [hcase V U hVc hUc hd.symm (union_comm U V ▸ hcover) h]
    exact hUc

end CircleDomainRigidity

end

end OAI
