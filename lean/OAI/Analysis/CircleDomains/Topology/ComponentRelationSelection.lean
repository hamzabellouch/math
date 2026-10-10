import OAI.Analysis.CircleDomains.Topology.ClosedComponentCorrespondence
import OAI.Analysis.CircleDomains.Topology.ClosedRelationNeighborhood

namespace OAI

/-! Actual selections from the matched component correspondence. They
agree with the conformal map on the domain, are constant on each omitted
component, and are continuous at every singleton target fiber. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 def targetFiber (q : Sphere) : Set Sphere := {p | D.componentRelation q p}

 theorem targetFiber_nonempty (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) (q : Sphere) : (D.targetFiber q).Nonempty := by
  by_cases hq : q ∈ G
  · exact ⟨f q,D.componentRelation_graph hf hq⟩
  · obtain ⟨p,hp,he⟩ := D.componentRelation_source_fiber hG hf hq
    refine ⟨p,?_⟩
    change p ∈ {p' | D.componentRelation q p'}
    rw [he]
    exact mem_connectedComponentIn hp

 def selectedTarget (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    (q : Sphere) : Sphere := (D.targetFiber_nonempty hG hf q).some

 theorem selectedTarget_mem (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    (q : Sphere) : D.componentRelation q (D.selectedTarget hG hf q) :=
  (D.targetFiber_nonempty hG hf q).some_mem

 theorem selectedTarget_on_domain (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    {q : Sphere} (hq : q ∈ G) : D.selectedTarget hG hf q = f q :=
  D.componentRelation_on_domain hq (D.selectedTarget_mem hG hf q)

 theorem componentRelation_source_saturated (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {q q' p : Sphere}
    (hq : q ∈ Gᶜ) (hqq : q' ∈ connectedComponentIn Gᶜ q)
    (hr : D.componentRelation q p) : D.componentRelation q' p := by
  obtain ⟨t,ht,he⟩ := D.componentRelation_source_fiber hG hf hq
  have hp : p ∈ (f '' G)ᶜ := by
    apply connectedComponentIn_subset (f '' G)ᶜ t
    rw [← he]
    exact hr
  obtain ⟨s,hs,hse⟩ := D.componentRelation_target_fiber hG hf hp
  have hqs : q ∈ connectedComponentIn Gᶜ s := by
    rw [← hse]
    exact hr
  have hcc : connectedComponentIn Gᶜ q = connectedComponentIn Gᶜ s :=
    (connectedComponentIn_eq hqs).symm
  change q' ∈ {q' | D.componentRelation q' p}
  rw [hse,← hcc]
  exact hqq

 theorem targetFiber_eq_on_component (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {q q' : Sphere}
    (hq : q ∈ Gᶜ) (hqq : q' ∈ connectedComponentIn Gᶜ q) :
    D.targetFiber q = D.targetFiber q' := by
  have hq' : q' ∈ Gᶜ := connectedComponentIn_subset _ _ hqq
  have hback : q ∈ connectedComponentIn Gᶜ q' := by
    rw [← connectedComponentIn_eq hqq]
    exact mem_connectedComponentIn hq
  ext p
  exact ⟨D.componentRelation_source_saturated hG hf hq hqq,
    D.componentRelation_source_saturated hG hf hq' hback⟩

 theorem selectedTarget_eq_on_component (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {q q' : Sphere}
    (hq : q ∈ Gᶜ) (hqq : q' ∈ connectedComponentIn Gᶜ q) :
    D.selectedTarget hG hf q = D.selectedTarget hG hf q' := by
  unfold selectedTarget
  simp only [D.targetFiber_eq_on_component hG hf hq hqq]

 theorem selectedTarget_continuousAt (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {q p : Sphere}
    (hsingle : D.targetFiber q = {p}) : ContinuousAt (D.selectedTarget hG hf) q := by
  apply closed_relation_selection_continuousAt (D.componentRelation_closed hf)
    _ (D.selectedTarget_mem hG hf)
  intro y hy
  have hy' : y = p := mem_singleton_iff.mp (hsingle ▸ hy)
  have hsel : D.selectedTarget hG hf q = p :=
    mem_singleton_iff.mp (hsingle ▸ D.selectedTarget_mem hG hf q)
  exact hy'.trans hsel.symm

 theorem selectedScalar_neighborhood (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {φ : Sphere → ℝ} (hφ : Continuous φ)
    {K : Set Sphere} {a b : ℝ}
    (hK : ∀ q ∈ K, ∀ p, D.componentRelation q p → φ p ∈ Ioo a b) :
    ∃ V : Set Sphere, IsOpen V ∧ K ⊆ V ∧
      ∀ q ∈ V, φ (D.selectedTarget hG hf q) ∈ Ioo a b := by
  obtain ⟨V,hV,hKV,hmap⟩ := closed_relation_neighborhood (D.componentRelation_closed hf)
    (isOpen_Ioo.preimage hφ) hK
  exact ⟨V,hV,hKV,fun q hq => hmap q hq _ (D.selectedTarget_mem hG hf q)⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
