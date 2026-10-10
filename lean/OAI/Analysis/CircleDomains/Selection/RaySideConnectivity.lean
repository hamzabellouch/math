import OAI.Analysis.CircleDomains.Topology.RayJordanSides
import OAI.Analysis.CircleDomains.Topology.CrosscutSeparationInput

namespace OAI

/-! Both sides of each compactified lifted ray are connected. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.HalfPlaneRay

theorem subset_complement (R : HalfPlaneRay) (H : ℂ ≃ₜ ℂ)
    (hf : R.IsJordan H) :
    jordanInterior H ⊆ Metric.ball 0 1 \ range R.crosscut := by
  intro z hz
  refine ⟨(R.filling_subset hf).2 hz, ?_⟩
  intro hp
  have hfront : z ∈ frontier (jordanInterior H) := hf ▸ Or.inl hp
  have hi : z ∈ interior (jordanInterior H) := by
    simpa only [(jordanInterior_isOpen H).interior_eq] using hz
  exact Set.disjoint_left.mp disjoint_interior_frontier hi hfront

theorem component_in_or_out (R : HalfPlaneRay) (H : ℂ ≃ₜ ℂ)
    (hf : R.IsJordan H)
    {V : Set ℂ} (hV : IsPreconnected V)
    (hsub : V ⊆ Metric.ball 0 1 \ range R.crosscut) :
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
      · have hn : ‖boundaryClosingArc _ R.crosscut_start_norm t‖ < 1 := by
          simpa only [Metric.mem_ball, dist_zero_right] using (hsub hz).1
        rw [boundaryClosingArc_norm] at hn
        exact lt_irrefl _ hn

theorem exterior_connected (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) (H : ℂ ≃ₜ ℂ)
    (hf : R.IsJordan H) :
    IsConnected (Metric.ball 0 1 \ closure (jordanInterior H)) := by
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hd, hcover, _, _⟩ :=
    hsep R.crosscut.toContinuousMap R.compactify_injective
      R.crosscut_start_norm (by
        change ‖R.compactify ⊤‖ = 1
        rw [R.compactify_top, norm_one])
      R.crosscut_interior
  have hJsub := subset_complement R H hf
  have hJUorV : jordanInterior H ⊆ U ∨ jordanInterior H ⊆ V := by
    apply (isConnected_jordanInterior H).isPreconnected.subset_or_subset hUo hVo hd
    exact fun z hz => hcover ▸ hJsub hz
  have hcase (A B : Set ℂ) (hAc : IsConnected A) (hBc : IsConnected B)
      (hAB : Disjoint A B) (hc : A ∪ B = Metric.ball 0 1 \ range R.crosscut)
      (hJA : jordanInterior H ⊆ A) :
      Metric.ball 0 1 \ closure (jordanInterior H) = B := by
    have hAsub : A ⊆ Metric.ball 0 1 \ range R.crosscut := hc ▸ subset_union_left
    have hBsub : B ⊆ Metric.ball 0 1 \ range R.crosscut := hc ▸ subset_union_right
    have hAJ : A ⊆ jordanInterior H := by
      rcases component_in_or_out R H hf hAc.isPreconnected hAsub with h | h
      · exact h
      · obtain ⟨z, hz⟩ := (isConnected_jordanInterior H).nonempty
        exact (h (hJA hz) (subset_closure hz)).elim
    have hBout : B ⊆ (closure (jordanInterior H))ᶜ := by
      rcases component_in_or_out R H hf hBc.isPreconnected hBsub with h | h
      · obtain ⟨z, hz⟩ := hBc.nonempty
        exact (Set.disjoint_left.mp hAB (hJA (h hz)) hz).elim
      · exact h
    apply Subset.antisymm
    · intro z hz
      have hn : z ∉ range R.crosscut := by
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


theorem leftSide_connected (R : HalfPlaneRay) (H : ℂ ≃ₜ ℂ) (hf : R.IsJordan H) :
    IsConnected (closure (jordanInterior H) \ range R.crosscut) := by
  apply (isConnected_jordanInterior H).subset_closure
  · intro z hz
    exact ⟨subset_closure hz, (R.subset_complement H hf hz).2⟩
  · exact sdiff_subset

theorem rightSide_connected (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) (H : ℂ ≃ₜ ℂ) (hf : R.IsJordan H) :
    IsConnected (Metric.closedBall 0 1 \ closure (jordanInterior H)) := by
  apply (R.exterior_connected hsep H hf).subset_closure
  · exact sdiff_subset_sdiff_left Metric.ball_subset_closedBall
  · intro z hz
    have hh : z ∈ (closure (jordanInterior H))ᶜ ∩ closure (Metric.ball (0 : ℂ) 1) := by
      refine ⟨hz.2, ?_⟩
      simpa only [closure_ball _ one_ne_zero] using hz.1
    have hi := isClosed_closure.isOpen_compl.inter_closure hh
    change z ∈ closure (Metric.ball 0 1 ∩ (closure (jordanInterior H))ᶜ)
    simpa only [inter_comm] using hi

end CircleDomainRigidity.HalfPlaneRay

end

end OAI
