import OAI.Analysis.CircleDomains.Topology.FiniteClopenRefinement
import Mathlib.Topology.Separation.Regular

namespace OAI

/-! Finite disjoint closed sets have disjoint closed neighborhoods
subordinate to individually prescribed open sets. -/
open Set Topology
noncomputable section
namespace CircleDomainRigidity

lemma finite_disjoint_closed_neighborhoods
    {X I : Type*} [TopologicalSpace X] [NormalSpace X] [Finite I]
    (A O : I → Set X) (hA : ∀ i, IsClosed (A i))
    (hO : ∀ i, IsOpen (O i)) (hAO : ∀ i, A i ⊆ O i)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ∃ U : I → Set X, (∀ i, IsOpen (U i)) ∧ (∀ i, A i ⊆ U i) ∧
      (∀ i, closure (U i) ⊆ O i) ∧
      Pairwise (fun i j => Disjoint (closure (U i)) (closure (U j))) := by
  classical
  let B (i : I) := ⋃ j : {j : I // j≠i}, A j.val
  have hB (i : I) : IsClosed (B i) := isClosed_iUnion_of_finite (fun j => hA j.val)
  have hAB (i : I) : A i ⊆ O i \ B i := by
    intro x hx
    refine ⟨hAO i hx,?_⟩
    intro hb
    obtain ⟨j,hj⟩ := mem_iUnion.mp hb
    exact Set.disjoint_left.mp (hd j.property.symm) hx hj
  choose Z hZo hAZ hZsub using fun i =>
    normal_exists_closure_subset (hA i) ((hO i).sdiff (hB i)) (hAB i)
  let V (i : I) := Z i \ ⋃ j : {j : I // j≠i}, closure (Z j.val)
  have hVo (i : I) : IsOpen (V i) :=
    (hZo i).sdiff (isClosed_iUnion_of_finite fun _ => isClosed_closure)
  have hAV (i : I) : A i ⊆ V i := by
    intro x hx
    refine ⟨hAZ i hx,?_⟩
    intro hb
    obtain ⟨j,hj⟩ := mem_iUnion.mp hb
    exact (hZsub j.val hj).2 (mem_iUnion.mpr ⟨⟨i,j.property.symm⟩,hx⟩)
  have hVd : Pairwise (fun i j => Disjoint (V i) (V j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact hxi.2 (mem_iUnion.mpr ⟨⟨j,hij.symm⟩,subset_closure hxj.1⟩)
  choose U hUo hAU hUV using fun i =>
    normal_exists_closure_subset (hA i) (hVo i) (hAV i)
  refine ⟨U,hUo,hAU,?_,?_⟩
  · intro i x hx
    exact (hZsub i (subset_closure (hUV i hx).1)).1
  · intro i j hij
    exact (hVd hij).mono (hUV i) (hUV j)

end CircleDomainRigidity

end

end OAI
