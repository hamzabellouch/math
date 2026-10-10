import OAI.MeasureTheory.Falconer.Recursion.MinimalDescriptorLength
import OAI.MeasureTheory.Falconer.Recursion.PrefixMass

namespace OAI

namespace PlanarFalconer
open Set

theorem suffix_projection_mem (A : ℕ → ℝ) {N q a t : ℕ}
    (ht : t ≤ N) (hw : a+100*q < t)
    (hs : a+t < 2*policyDepth A N q a t) :
    PolicyDescriptor.projection (policyDepth A N q a t) t ∈
      policyDescriptorList A N q a t := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨(a,t),?_,?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,
      le_rfl,le_rfl,hw⟩
  · apply Finset.mem_union_right
    simp [hs]

theorem policyDescriptor_anchor_le_end (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) {b : PolicyDescriptor}
    (hb : b ∈ policyDescriptorList A N q a t) : descriptorAnchor b ≤ t := by
  obtain ⟨_,u,_,hut,_,_,_,_,hu⟩ := policyDescriptor_origin A hq hb
  omega

theorem DyadicSquare.eq_take_of_mem (Q : DyadicSquare) (hQ : 0 < Q.side)
    {P C : CellPath} {n : ℕ} (hP : P.length = n) (hn : n ≤ C.length)
    {x : Plane} (hxP : x ∈ (Q.descendant P).carrier)
    (hxC : x ∈ (Q.descendant C).carrier) : P = C.take n := by
  by_contra hne
  have hl : P.length = (C.take n).length := by simp [hP,List.length_take,hn]
  exact Set.disjoint_left.mp (Q.descendants_disjoint hQ hl hne) hxP
    (Q.descendant_subset_take hQ C n hxC)

theorem DyadicSquare.same_ancestor (Q : DyadicSquare) (hQ : 0 < Q.side)
    {P C : CellPath} {n : ℕ} (hP : P.length = n) (hn : n ≤ C.length)
    {x y : Plane} (hxP : x ∈ (Q.descendant P).carrier)
    (hxC : x ∈ (Q.descendant C).carrier) (hyC : y ∈ (Q.descendant C).carrier) :
    y ∈ (Q.descendant P).carrier := by
  rw [Q.eq_take_of_mem hQ hP hn hxP hxC]
  exact Q.descendant_subset_take hQ C n hyC

end PlanarFalconer

end OAI
