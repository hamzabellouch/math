import OAI.Analysis.CircleDomains.Topology.DiskCrosscutJordan
import OAI.Analysis.CircleDomains.Topology.DiskBoundarySide

namespace OAI

/-! A connected set in the closed disk avoiding a crosscut cannot join
its two boundary arcs. This includes continua that run along the circle. -/
open Set Function Metric Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma crosscut_closed_side_locally_open {a : ℂ} (p : Path a 1) (ha : ‖a‖ = 1)
    (H : ℂ ≃ₜ ℂ)
    (hf : frontier (jordanInterior H) = range p ∪ range (boundaryClosingArc a ha))
    (hinside : jordanInterior H ⊆ ball (0 : ℂ) 1)
    {z : ℂ} (hz : z ∈ closure (jordanInterior H)) (hzp : z ∉ range p) :
    ∃ ε > 0, ball z ε ∩ closedBall (0 : ℂ) 1 ⊆ closure (jordanInterior H) := by
  by_cases hzJ : z ∈ jordanInterior H
  · obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (jordanInterior_isOpen H) z hzJ
    exact ⟨ε,hε,fun _ h => subset_closure (hball h.1)⟩
  · have hzf : z ∈ frontier (jordanInterior H) := by
      rw [(jordanInterior_isOpen H).frontier_eq]
      exact ⟨hz,hzJ⟩
    have hc : IsClosed (range p) := (isCompact_range p.continuous).isClosed
    obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hc.isOpen_compl z hzp
    refine ⟨ε,hε,closed_disk_neighborhood_in_filling H hinside hzf hε ?_⟩
    rintro w ⟨hw,hwf⟩
    rw [hf] at hwf
    rcases hwf with hwp | ⟨t,rfl⟩
    · exact (hball hw hwp).elim
    · exact mem_sphere_zero_iff_norm.mpr (boundaryClosingArc_norm a ha t)

lemma connected_avoiding_crosscut_one_side {a : ℂ} (p : Path a 1) (ha : ‖a‖ = 1)
    (H : ℂ ≃ₜ ℂ)
    (hf : frontier (jordanInterior H) = range p ∪ range (boundaryClosingArc a ha))
    (hinside : jordanInterior H ⊆ ball (0 : ℂ) 1)
    {B : Set ℂ} (hB : IsPreconnected B) (hBd : B ⊆ closedBall (0 : ℂ) 1)
    (hBp : Disjoint B (range p)) :
    B ⊆ closure (jordanInterior H) ∨ B ⊆ (closure (jordanInterior H))ᶜ := by
  let T : Set B := {z | (z : ℂ) ∈ closure (jordanInterior H)}
  let : PreconnectedSpace B := isPreconnected_iff_preconnectedSpace.mp hB
  have hc : IsClosed T := isClosed_closure.preimage continuous_subtype_val
  have ho : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨ε,hε,hball⟩ := crosscut_closed_side_locally_open p ha H hf hinside hz
      (fun h => Set.disjoint_left.mp hBp z.property h)
    have hn : ∀ᶠ w : B in 𝓝 z, (w : ℂ) ∈ ball z.val ε :=
      continuous_subtype_val.continuousAt.eventually (isOpen_ball.mem_nhds (mem_ball_self hε))
    filter_upwards [hn] with w hw
    exact hball ⟨hw,hBd w.property⟩
  by_cases hn : T.Nonempty
  · left
    have h := (show IsClopen T from ⟨hc,ho⟩).eq_univ hn
    intro z hz
    have hzT : (⟨z,hz⟩ : B) ∈ T := h.symm ▸ mem_univ _
    exact hzT
  · right
    intro z hz hzc
    exact hn ⟨⟨z,hz⟩,hzc⟩

end CircleDomainRigidity

end

end OAI
