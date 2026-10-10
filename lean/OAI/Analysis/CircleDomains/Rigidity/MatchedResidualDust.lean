import OAI.Analysis.CircleDomains.Topology.PlaneComponentRelation
import OAI.Analysis.CircleDomains.Topology.BoundaryBumping

namespace OAI

/-! Covering the indexed pairs removes every non-point component. The
remaining closed set is removable dust on the original boundary. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem unindexed_components_singleton
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hG' : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {q : Sphere} (hq : q ∈ Gᶜ) (hnot : ∀ j : D.IndexedMatchedPair, q ∉ j.val.1) :
    connectedComponentIn Gᶜ q = {q} ∧ ∃ p, D.targetFiber q = {p} := by
  obtain ⟨P,hP,hPe⟩ := D.exists_matched_pair_of_source hG.1 hf hq
  have hqP : q ∈ P.1 := by rw [hPe]; exact mem_connectedComponentIn hq
  rcases D.matched_pair_indexed_or_common_point hG hinf hG' hinf' hP with hi | ⟨hs,ht⟩
  · exact (hnot ⟨P,hP,hi⟩ hqP).elim
  · obtain ⟨x,hx⟩ := hs
    obtain ⟨p,hp⟩ := ht
    have hqx : q = x := mem_singleton_iff.mp (hx ▸ hqP)
    refine ⟨hPe.symm.trans (hx.trans (congrArg singleton hqx.symm)),p,?_⟩
    exact (hP.2.2 q hqP).trans hp

 theorem indexed_cover_residual_dust
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hG' : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {O : Set Sphere} (hO : IsOpen O) (hGO : G ⊆ O)
    (hcover : ∀ j : D.IndexedMatchedPair, j.val.1 ⊆ O) :
    IsCompact Oᶜ ∧ IsTotallyDisconnected Oᶜ ∧ Oᶜ ⊆ frontier G ∧
      ∀ q ∈ Oᶜ, connectedComponentIn Gᶜ q = {q} ∧ ∃ p, D.targetFiber q = {p} := by
  have hsingle (q : Sphere) (hq : q ∈ Oᶜ) :=
    D.unindexed_components_singleton hG hinf hf hG' hinf'
      (fun h => hq (hGO h)) (fun j hj => hq (hcover j hj))
  refine ⟨hO.isClosed_compl.isCompact,?_,?_,hsingle⟩
  · intro S hS hSc x hx y hy
    have hycc := hSc.subset_connectedComponentIn hx
      (fun z hz hzg => hS hz (hGO hzg)) hy
    change y ∈ connectedComponentIn Gᶜ x at hycc
    rw [(hsingle x (hS hx)).1,mem_singleton_iff] at hycc
    exact hycc.symm
  · intro q hq
    have hproper : Gᶜ ≠ univ := by
      intro he
      have hi : OnePoint.infty ∈ Gᶜ := he.symm ▸ mem_univ _
      exact hi hinf
    obtain ⟨p,hp,hpf⟩ := component_meets_frontier hG.1.isClosed_compl hproper
      (show q ∈ Gᶜ from fun h => hq (hGO h))
    have hpq : p = q := mem_singleton_iff.mp ((hsingle q hq).1 ▸ hp)
    simpa only [frontier_compl,hpq] using hpf

 theorem indexed_cover_residual_removable
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hG' : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    (hrem : IsConformallyRemovable (frontier G))
    {O : Set Sphere} (hO : IsOpen O) (hGO : G ⊆ O)
    (hcover : ∀ j : D.IndexedMatchedPair, j.val.1 ⊆ O) :
    IsConformallyRemovable Oᶜ := by
  obtain ⟨hK,_,hsub,_⟩ := D.indexed_cover_residual_dust hG hinf hf hG' hinf' hO hGO hcover
  exact hrem.of_isCompact_subset hK hsub

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
