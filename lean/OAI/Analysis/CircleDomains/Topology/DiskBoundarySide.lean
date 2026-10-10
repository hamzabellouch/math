import OAI.Analysis.CircleDomains.Topology.DiskRaySides
import Mathlib.Analysis.Convex.Topology

namespace OAI

/-! Away from the crosscut, a boundary arc of a filling has a whole relative
neighborhood in the closed disk on the same side. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem closed_disk_neighborhood_in_filling
    (H : ℂ ≃ₜ ℂ) (hU : jordanInterior H ⊆ Metric.ball 0 1)
    {x : ℂ} (hx : x ∈ frontier (jordanInterior H))
    {ε : ℝ} (hε : 0 < ε)
    (hfront : Metric.ball x ε ∩ frontier (jordanInterior H) ⊆ Metric.sphere 0 1) :
    Metric.ball x ε ∩ Metric.closedBall 0 1 ⊆ closure (jordanInterior H) := by
  have hC : IsPreconnected (Metric.ball x ε ∩ Metric.ball (0 : ℂ) 1) :=
    ((convex_ball x ε).inter (convex_ball (0 : ℂ) 1)).isPreconnected
  have hmiss : Disjoint (Metric.ball x ε ∩ Metric.ball (0 : ℂ) 1)
      (frontier (jordanInterior H)) := by
    apply Set.disjoint_left.mpr
    intro z hz hf
    have hn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp (hfront ⟨hz.1, hf⟩)
    have hl : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz.2
    exact (ne_of_lt hl) hn
  have hsplit : Metric.ball x ε ∩ Metric.ball (0 : ℂ) 1 ⊆ jordanInterior H ∨
      Metric.ball x ε ∩ Metric.ball (0 : ℂ) 1 ⊆ (closure (jordanInterior H))ᶜ := by
    apply hC.subset_or_subset (jordanInterior_isOpen H) isClosed_closure.isOpen_compl
    · exact disjoint_compl_right.mono_left subset_closure
    · intro z hz
      by_cases hi : z ∈ jordanInterior H
      · exact Or.inl hi
      · right
        intro hc
        apply Set.disjoint_left.mp hmiss hz
        rw [(jordanInterior_isOpen H).frontier_eq]
        exact ⟨hc, hi⟩
  have hinside : Metric.ball x ε ∩ Metric.ball (0 : ℂ) 1 ⊆ jordanInterior H := by
    rcases hsplit with hi | ho
    · exact hi
    · obtain ⟨z, hzB, hzU⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hx)
        (Metric.ball x ε) (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
      exact (ho ⟨hzB, hU hzU⟩ (subset_closure hzU)).elim
  intro z hz
  apply closure_mono hinside
  apply Metric.isOpen_ball.inter_closure
  simpa only [closure_ball _ one_ne_zero] using hz

theorem diskRay_left_boundary_neighborhood (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (H : ℂ ≃ₜ ℂ)
    (hf : frontier (jordanInterior H) = range (diskRayCrosscut γ hγ) ∪
      range (boundaryClosingArc _ (compactifiedDiskRay_start_norm hγ)))
    {x : ℂ} (hx : x ∈ frontier (jordanInterior H))
    (hmiss : x ∉ range (diskRayCrosscut γ hγ)) :
    ∃ ε > 0, Metric.ball x ε ∩ Metric.closedBall 0 1 ⊆ closure (jordanInterior H) := by
  have hclosed : IsClosed (range (diskRayCrosscut γ hγ)) :=
    (isCompact_range (diskRayCrosscut γ hγ).continuous).isClosed
  obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl x hmiss
  refine ⟨ε, hε, closed_disk_neighborhood_in_filling H
    (diskRayJordan_filling_subset γ hγ H hf).2 hx hε ?_⟩
  rintro z ⟨hzB, hzf⟩
  rw [hf] at hzf
  rcases hzf with hp | ⟨t, rfl⟩
  · exact (hB hzB hp).elim
  · exact mem_sphere_zero_iff_norm.mpr (boundaryClosingArc_norm _ _ t)

end CircleDomainRigidity

end

end OAI
