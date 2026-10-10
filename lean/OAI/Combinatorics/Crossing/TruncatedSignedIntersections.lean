import OAI.Combinatorics.Crossing.UniformTrackPerturbation
import OAI.Combinatorics.Crossing.RowCrossingCount

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
open scoped BigOperators
variable {m n : ℕ} {D : ContinuousDrawing m n} (V : VertexTruncation D)

theorem piece_subset_range (e : BipartiteEdge m n) (i : ℕ) (hi : i<V.pieces e) :
    segment ℝ (V.vertices e i) (V.vertices e (i+1)) ⊆ Set.range (V.path e) := by
  exact ((V.chain e).truncated (V.pieces_pos e) V.radius V.radius_pos
    (V.weak_short e).1 (V.weak_short e).2).piece_subset_path_range i hi

def signedIntersection (e f : BipartiteEdge m n) : ℝ :=
  if e=f then 0 else polygonIntersection (V.vertices e) (V.vertices f) (V.pieces e) (V.pieces f)

theorem signedIntersection_self (e : BipartiteEdge m n) : V.signedIntersection e e=0 := by
  simp [signedIntersection]

theorem signedIntersection_swap (e f : BipartiteEdge m n) : V.signedIntersection f e = -V.signedIntersection e f := by
  by_cases h : e=f
  · subst f
    simp [V.signedIntersection_self]
  · simp only [signedIntersection,ite_eq_right h,ite_eq_right (Ne.symm h)]
    exact polygonIntersection_swap _ _ _ _

theorem signedIntersection_zero_of_pairCrossings_empty {A : AdmissibleDrawing m n}
    (V : VertexTruncation A.toContinuousDrawing) (e f : BipartiteEdge m n)
    (hempty : pairCrossings A e f=∅) : V.signedIntersection e f=0 := by
  classical
  by_cases hef : e=f
  · subst f
    exact V.signedIntersection_self e
  · rw [signedIntersection,ite_eq_right hef]
    unfold polygonIntersection
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    have hnot : ¬ SegmentsCrossProperly (V.vertices e i) (V.vertices e (i+1))
        (V.vertices f j) (V.vertices f (j+1)) := by
      rintro ⟨_,s,hs,t,ht,he⟩
      let x := segmentPoint (V.vertices e i) (V.vertices e (i+1)) s
      have hxe : x ∈ edgeInterior A.toContinuousDrawing e := by
        apply V.range_subset_edgeInterior e
        apply V.piece_subset_range e i (Finset.mem_range.mp hi)
        rw [← Path.range_segment]
        exact ⟨⟨s,⟨hs.1.le,hs.2.le⟩⟩,by simp only [Path.segment_apply,AffineMap.lineMap_apply_module,x,segmentPoint]⟩
      have hxf : x ∈ edgeInterior A.toContinuousDrawing f := by
        apply V.range_subset_edgeInterior f
        apply V.piece_subset_range f j (Finset.mem_range.mp hj)
        rw [← Path.range_segment]
        refine ⟨⟨t,⟨ht.1.le,ht.2.le⟩⟩,?_⟩
        simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,x,segmentPoint] using he.symm
      have hx : x ∈ pairCrossings A e f := by
        apply Finset.mem_filter.mpr
        exact ⟨by simpa using (show x ∈ crossingPoints A.toContinuousDrawing from ⟨e,f,hef,hxe,hxf⟩),hef,hxe,hxf⟩
      rw [hempty] at hx
      exact Finset.notMem_empty x hx
    simp [segmentCrossingSign,hnot]

theorem pairCrossings_pos_of_signedIntersection_ne_zero {A : AdmissibleDrawing m n}
    (V : VertexTruncation A.toContinuousDrawing) (e f : BipartiteEdge m n)
    (h : V.signedIntersection e f ≠ 0) : 0 < (pairCrossings A e f).card := by
  by_contra hh
  have hz : (pairCrossings A e f).card=0 := by omega
  exact h (V.signedIntersection_zero_of_pairCrossings_empty e f (Finset.card_eq_zero.mp hz))

theorem signedIntersection_adjacent_zero {A : AdmissibleDrawing m n}
    (V : VertexTruncation A.toContinuousDrawing) (hnorm : NoAdjacentCrossings A)
    (e f : BipartiteEdge m n) (hadj : e.1=f.1 ∨ e.2=f.2) : V.signedIntersection e f=0 :=
  V.signedIntersection_zero_of_pairCrossings_empty e f (pairCrossings_eq_empty_of_adjacent A hnorm e f hadj)

end Zarankiewicz.VertexTruncation

end

end OAI
