import OAI.Analysis.CircleDomains.Topology.ConnectedIndexedNeighborhood
import OAI.Analysis.CircleDomains.Rigidity.MatchedMaskSupport

namespace OAI

/-! The open domain of the actual mask is connected, and its residual
complement is removable dust on the original circle-domain boundary. -/
open Set Function Filter Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}
variable [Encodable D.IndexedMatchedPair]

 theorem MatchedRoundDisks.exists_mask_domain (E : D.MatchedRoundDisks)
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hG' : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    (hrem : IsConformallyRemovable (frontier G))
    {φ : Sphere → ℝ} (hφ : Continuous φ) {L : ℝ≥0}
    (hL : LipschitzWith L (fun z : ℂ => φ (z : Sphere)))
    (m : ℕ) {cutoff : ℕ → ℂ → ℝ} (hc : ∀ n z, cutoff n z ∈ Icc (0:ℝ) 1)
    (hcc : ∀ n, Continuous (cutoff n))
    (hzero : ∀ n z, ‖z-E.traceCenter n‖ ≤
      traceBalloonInnerRatio m*traceBalloonRadius E.traceRadius m n → cutoff n z = 0)
    (hout : ∀ n z, traceBalloonRadius E.traceRadius m n ≤ ‖z-E.traceCenter n‖ → cutoff n z = 1) :
    ∃ W : D.IndexedMatchedPair → Set ℂ,
      (∀ j, IsOpen (W j)) ∧
      (∀ j, closedBall (E.sourceCenter j) (E.sourceRadius j) ⊆ W j) ∧
      (∀ j z, z ∈ W j → cutoff (Encodable.encode j) z = 0 ∧
        φ (D.selectedTarget hG.1 hf (z : Sphere)) ∈ E.traceInterval hG.1 hf φ L (Encodable.encode j)) ∧
      IsOpen (G ∪ ⋃ j, ((↑) : ℂ → Sphere) '' W j) ∧
      IsConnected (G ∪ ⋃ j, ((↑) : ℂ → Sphere) '' W j) ∧
      IsTotallyDisconnected (G ∪ ⋃ j, ((↑) : ℂ → Sphere) '' W j)ᶜ ∧
      IsConformallyRemovable (G ∪ ⋃ j, ((↑) : ℂ → Sphere) '' W j)ᶜ := by
  have hlocal (j : D.IndexedMatchedPair) : ∃ W : Set ℂ,
      IsOpen W ∧ IsConnected W ∧ closedBall (E.sourceCenter j) (E.sourceRadius j) ⊆ W ∧
      (W ∩ {z : ℂ | (z : Sphere) ∈ G}).Nonempty ∧
      ∀ z ∈ W, cutoff (Encodable.encode j) z = 0 ∧
        φ (D.selectedTarget hG.1 hf (z : Sphere)) ∈ E.traceInterval hG.1 hf φ L (Encodable.encode j) := by
    obtain ⟨V,hV,hKV,_,hv⟩ := E.mask_indexed_neighborhood hG.1 hf hφ hL m hc hcc hzero hout 0 j
    obtain ⟨W,hW,hWc,hWV,hKW,hm⟩ := E.connected_neighborhood j hV hKV
    exact ⟨W,hW,hWc,hKW,hm,fun z hz => hv z (hWV hz)⟩
  choose W hW hWc hKW hm hp using hlocal
  let O := G ∪ ⋃ j, ((↑) : ℂ → Sphere) '' W j
  have hO : IsOpen O := hG.1.union (isOpen_iUnion (fun j => OnePoint.isOpen_image_coe.mpr (hW j)))
  have hcover (j : D.IndexedMatchedPair) : j.val.1 ⊆ O := by
    rw [E.source_eq]
    rintro _ ⟨z,hz,rfl⟩
    exact Or.inr (mem_iUnion.mpr ⟨j,mem_image_of_mem _ (hKW j hz)⟩)
  have hdust := D.indexed_cover_residual_dust hG hinf hf hG' hinf' hO subset_union_left hcover
  exact ⟨W,hW,hKW,hp,hO,connected_indexed_union hG.2.1 hinf hWc hm,hdust.2.1,
    hrem.of_isCompact_subset hdust.1 hdust.2.2.1⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
