import OAI.Analysis.CircleDomains.Topology.ClopenNeighborhood
import OAI.Analysis.CircleDomains.Topology.FiniteClopenRefinement

namespace OAI

/-! A componentwise open cover of a compact Hausdorff space has a finite
disjoint clopen refinement. This is the finite decomposition used before
choosing small ambient Jordan neighborhoods. -/
open Set Topology
noncomputable section
namespace CircleDomainRigidity

lemma compact_clopen_partition_of_component_cover
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (O : X → Set X) (hO : ∀ x, IsOpen (O x))
    (hcomp : ∀ x, connectedComponent x ⊆ O x) :
    ∃ (s : Finset X) (C : s → Set X),
      (∀ i, IsClopen (C i)) ∧
      Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      (⋃ i, C i) = univ ∧ ∀ i, C i ⊆ O i.val := by
  classical
  choose V hV hxV hVO using fun x =>
    exists_clopen_between_component_and_open x (hO x) (hcomp x)
  have hcover : (univ : Set X) ⊆ ⋃ x, V x := by
    intro x _
    exact mem_iUnion.mpr ⟨x,hxV x⟩
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover V (fun x => (hV x).isOpen) hcover
  obtain ⟨C,hC,hd,hCV,hcov⟩ := finite_disjoint_clopen_refinement s
    (fun i => V i.val) (fun i => hV i.val)
  refine ⟨s,C,hC,hd,?_,fun i => (hCV i).trans (hVO i.val)⟩
  rw [hcov]
  apply eq_univ_of_forall
  intro x
  obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  exact mem_iUnion.mpr ⟨⟨i,hi⟩,hxi⟩

end CircleDomainRigidity

end

end OAI
