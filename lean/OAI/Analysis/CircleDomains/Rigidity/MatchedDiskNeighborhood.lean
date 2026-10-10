import OAI.Analysis.CircleDomains.Rigidity.FiniteMatchedField
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-! Uniform upper control of the actual selected field on circles shrinking
to an indexed source disk, including point-to-disk matches. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem selectedPlane_near_indexed_disk
    (E : D.MatchedRoundDisks) (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G))
    (j : D.IndexedMatchedPair) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ closedBall (E.sourceCenter j) (E.sourceRadius j+δ),
      ‖D.selectedPlane hG hf z-E.targetCenter j‖ < E.targetRadius j+ε := by
  let U : Set Sphere := ((↑) : ℂ → Sphere) '' ball (E.targetCenter j) (E.targetRadius j+ε)
  have hU : IsOpen U := OnePoint.isOpenEmbedding_coe.isOpenMap _ isOpen_ball
  obtain ⟨V,hV,hKV,hrel⟩ := closed_relation_neighborhood (D.componentRelation_closed hf)
    (K := j.val.1) hU (by
      intro q hq p hp
      have hpt : p ∈ j.val.2 := by
        rw [← j.property.1.2.2 q hq]
        exact hp
      rw [E.target_eq] at hpt
      obtain ⟨w,hw,rfl⟩ := hpt
      exact mem_image_of_mem _ (show w ∈ ball (E.targetCenter j) (E.targetRadius j+ε) from
        lt_of_le_of_lt hw (lt_add_of_pos_right _ hε)))
  have hVp : IsOpen (((↑) : ℂ → Sphere) ⁻¹' V) := hV.preimage OnePoint.continuous_coe
  have hsub : closedBall (E.sourceCenter j) (E.sourceRadius j) ⊆ ((↑) : ℂ → Sphere) ⁻¹' V := by
    intro z hz
    apply hKV
    rw [E.source_eq]
    exact mem_image_of_mem _ hz
  obtain ⟨δ,hδ,hd⟩ := (isCompact_closedBall (E.sourceCenter j) (E.sourceRadius j)).exists_cthickening_subset_open
    hVp hsub
  have hδsub : closedBall (E.sourceCenter j) (E.sourceRadius j+δ) ⊆
      ((↑) : ℂ → Sphere) ⁻¹' V := by
    simpa only [cthickening_closedBall hδ.le (E.source_nonneg j),add_comm δ] using hd
  refine ⟨δ,hδ,?_⟩
  intro z hz
  have hp := hrel (z : Sphere) (hδsub hz) _ (D.selectedTarget_mem hG hf _)
  obtain ⟨w,hw,he⟩ := hp
  unfold selectedPlane
  rw [← he,finiteCoord_coe]
  simpa only [mem_ball,dist_eq_norm] using hw

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
