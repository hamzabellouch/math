import OAI.Combinatorics.Crossing.MarkedCurveDisks
import Mathlib.Topology.Separation.Regular

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem finite_compact_corridors {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K O : ι → Set Plane) (hK : ∀ i, IsCompact (K i))
    (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (hO : ∀ i, IsOpen (O i)) (hKO : ∀ i, K i ⊆ O i) :
    ∃ U : ι → Set Plane, (∀ i, IsOpen (U i)) ∧ (∀ i, K i ⊆ U i) ∧
      (∀ i, U i ⊆ O i) ∧ (∀ i j, i ≠ j → Disjoint (U i) (U j)) := by
  have hex (i j : ι) : ∃ A B : Set Plane, IsOpen A ∧ IsOpen B ∧ K i ⊆ A ∧ K j ⊆ B ∧
      (i ≠ j → Disjoint A B) := by
    by_cases he : i=j
    · exact ⟨Set.univ,Set.univ,isOpen_univ,isOpen_univ,Set.subset_univ _,Set.subset_univ _,fun hn => False.elim (hn he)⟩
    · obtain ⟨A,B,hA,hB,hi,hj,hab⟩ := normal_separation (hK i).isClosed (hK j).isClosed (hd i j he)
      exact ⟨A,B,hA,hB,hi,hj,fun _ => hab⟩
  choose A B hA hB hKA hKB hAB using hex
  let U : ι → Set Plane := fun i => O i ∩ ⋂ j, A i j ∩ B j i
  refine ⟨U,?_,?_,?_,?_⟩
  · intro i
    exact (hO i).inter (isOpen_iInter_of_finite (fun j => (hA i j).inter (hB j i)))
  · intro i x hx
    exact ⟨hKO i hx,Set.mem_iInter.mpr (fun j => ⟨hKA i j hx,hKB j i hx⟩)⟩
  · intro i x hx
    exact hx.1
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp (hAB i j hij)
      (Set.mem_iInter.mp hx.2 j).1 (Set.mem_iInter.mp hy.2 i).2

end Zarankiewicz

end

end OAI
