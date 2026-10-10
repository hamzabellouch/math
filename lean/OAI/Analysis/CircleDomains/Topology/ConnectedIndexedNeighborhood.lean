import OAI.Analysis.CircleDomains.Rigidity.MatchedMaskContinuity
import OAI.Analysis.CircleDomains.Rigidity.MatchedResidualDust
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Analysis.Normed.Module.Connected

namespace OAI

/-! Shrink each indexed plateau to its connected open component. It
still contains the whole disk and meets the original domain. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}

 theorem MatchedRoundDisks.connected_neighborhood (E : D.MatchedRoundDisks)
    (j : D.IndexedMatchedPair) {V : Set ℂ} (hV : IsOpen V)
    (hKV : closedBall (E.sourceCenter j) (E.sourceRadius j) ⊆ V) :
    ∃ W : Set ℂ, IsOpen W ∧ IsConnected W ∧ W ⊆ V ∧
      closedBall (E.sourceCenter j) (E.sourceRadius j) ⊆ W ∧
      (W ∩ {z : ℂ | (z : Sphere) ∈ G}).Nonempty := by
  let K := closedBall (E.sourceCenter j) (E.sourceRadius j)
  let W := connectedComponentIn V (E.sourceCenter j)
  have hcK : E.sourceCenter j ∈ K := mem_closedBall_self (E.source_nonneg j)
  have hcV : E.sourceCenter j ∈ V := hKV hcK
  have hKW : K ⊆ W := (isConnected_closedBall (E.source_nonneg j)).isPreconnected.subset_connectedComponentIn hcK hKV
  have hWopen : IsOpen W := hV.connectedComponentIn
  have hWconn : IsConnected W := isConnected_connectedComponentIn_iff.mpr hcV
  refine ⟨W,hWopen,hWconn,connectedComponentIn_subset _ _,hKW,?_⟩
  by_contra hnone
  have havoid : ((↑) : ℂ → Sphere) '' W ⊆ Gᶜ := by
    rintro _ ⟨z,hz,rfl⟩ hzg
    exact hnone ⟨z,hz,hzg⟩
  have hcim : (E.sourceCenter j : Sphere) ∈ ((↑) : ℂ → Sphere) '' W :=
    mem_image_of_mem _ (mem_connectedComponentIn hcV)
  have him := (hWconn.isPreconnected.image _ OnePoint.continuous_coe.continuousOn).subset_connectedComponentIn hcim havoid
  have hceq : connectedComponentIn Gᶜ (E.sourceCenter j : Sphere) = j.val.1 :=
    (j.property.1.1.eq_component_of_mem (E.source_center_mem j)).symm
  have hWK : W ⊆ K := by
    intro z hz
    have h := him (mem_image_of_mem _ hz)
    rw [hceq,E.source_eq,OnePoint.coe_injective.mem_set_image] at h
    exact h
  have he : K = W := Subset.antisymm hKW hWK
  have hKopen : IsOpen K := he ▸ hWopen
  exact (isCompact_closedBall (E.sourceCenter j) (E.sourceRadius j)).ne_univ
    ((show IsClopen K from ⟨isClosed_closedBall,hKopen⟩).eq_univ ⟨_,hcK⟩)

 theorem connected_indexed_union {ι : Type*} (hG : IsConnected G)
    (hinf : OnePoint.infty ∈ G) {W : ι → Set ℂ}
    (hW : ∀ j, IsConnected (W j))
    (hmeet : ∀ j, (W j ∩ {z : ℂ | (z : Sphere) ∈ G}).Nonempty) :
    IsConnected (G ∪ ⋃ j, ((↑) : ℂ → Sphere) '' W j) := by
  let O := G ∪ ⋃ j, ((↑) : ℂ → Sphere) '' W j
  refine ⟨⟨OnePoint.infty,Or.inl hinf⟩,isPreconnected_of_forall OnePoint.infty ?_⟩
  intro y hy
  rcases hy with hy | hy
  · exact ⟨G,subset_union_left,hinf,hy,hG.isPreconnected⟩
  · obtain ⟨j,hj⟩ := mem_iUnion.mp hy
    have him := (hW j).image _ OnePoint.continuous_coe.continuousOn
    have hmeet : (G ∩ ((↑) : ℂ → Sphere) '' W j).Nonempty := by
      obtain ⟨z,hz,hzg⟩ := hmeet j
      exact ⟨(z : Sphere),hzg,mem_image_of_mem _ hz⟩
    refine ⟨G ∪ ((↑) : ℂ → Sphere) '' W j,?_,Or.inl hinf,Or.inr hj,(hG.union hmeet him).isPreconnected⟩
    exact union_subset subset_union_left (fun z hz => Or.inr (mem_iUnion.mpr ⟨j,hz⟩))

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
