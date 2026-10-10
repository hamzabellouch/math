import OAI.Combinatorics.Crossing.ReducedCrossingCorners
import OAI.Combinatorics.Crossing.LocalSegmentTransversality
import OAI.Combinatorics.Crossing.LocallyTransverseNormalization

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem LocallyTransverseCrossings.exists_trace_lines (D : AdmissibleDrawing m n)
    (h : LocallyTransverseCrossings D) (e f : BipartiteEdge m n) (hef : e ≠ f)
    (x : Plane) (hxe : x ∈ edgeInterior D.toContinuousDrawing e)
    (hxf : x ∈ edgeInterior D.toContinuousDrawing f) :
    ∃ d k : Plane, det2 d k ≠ 0 ∧ ∃ U : Set Plane, IsOpen U ∧ x ∈ U ∧
      (∀ z ∈ U, z ∈ Set.range (D.edge e) → det2 d (z-x)=0) ∧
      (∀ z ∈ U, z ∈ Set.range (D.edge f) → det2 k (z-x)=0) := by
  obtain ⟨a,b,c,d,hdet,hxab,hxcd,U,hU,hxU,htraceE,htraceF⟩ := h e f hef x hxe hxf
  let V : Set Plane := Set.range D.vertex
  have hV : IsClosed V := (Set.finite_range D.vertex).isClosed
  have hxV : x ∉ V := by
    rintro ⟨j,hj⟩
    exact edgeInterior_not_vertex D.toContinuousDrawing e x hxe j hj.symm
  refine ⟨b-a,d-c,hdet,U ∩ Vᶜ,hU.inter hV.isOpen_compl,⟨hxU,hxV⟩,?_,?_⟩
  · intro z hz hze
    have hzi := edgeInterior_of_range_not_vertices D.toContinuousDrawing e z hze (by
      intro j hj
      exact hz.2 ⟨j,hj.symm⟩)
    exact det2_of_common_openSegment a b x z hxab ((htraceE z hz.1).mp hzi)
  · intro z hz hzf
    have hzi := edgeInterior_of_range_not_vertices D.toContinuousDrawing f z hzf (by
      intro j hj
      exact hz.2 ⟨j,hj.symm⟩)
    exact det2_of_common_openSegment c d x z hxcd ((htraceF z hz.1).mp hzi)

theorem minimum_piece_det_at_crossing (D : AdmissibleDrawing m n)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (e f : BipartiteEdge m n) (hef : e ≠ f)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (Q : PolygonalChain (Set.range (D.edge f)) (D.vertex (.inl f.1)) (D.vertex (.inr f.2)))
    (hP : ∀ R : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1))
      (D.vertex (.inr e.2)), P.pieces ≤ R.pieces)
    (hQ : ∀ R : PolygonalChain (Set.range (D.edge f)) (D.vertex (.inl f.1))
      (D.vertex (.inr f.2)), Q.pieces ≤ R.pieces)
    (i j : ℕ) (hi : i < P.pieces) (hj : j < Q.pieces) (x : Plane)
    (hxe : x ∈ edgeInterior D.toContinuousDrawing e) (hxf : x ∈ edgeInterior D.toContinuousDrawing f)
    (hxp : x ∈ segment ℝ (P.vertices i) (P.vertices (i+1)))
    (hxq : x ∈ segment ℝ (Q.vertices j) (Q.vertices (j+1))) :
    det2 (P.vertices (i+1)-P.vertices i) (Q.vertices (j+1)-Q.vertices j) ≠ 0 := by
  have hx : x ∈ crossingPoints D.toContinuousDrawing := ⟨e,f,hef,hxe,hxf⟩
  have hpo := minimum_piece_crossing_open D hstraight e P hP i hi x hx hxp
  have hqo := minimum_piece_crossing_open D hstraight f Q hQ j hj x hx hxq
  obtain ⟨d,k,hdk,U,hU,hxU,hlineP,hlineQ⟩ :=
    LocallyTransverseCrossings.exists_trace_lines D htrans e f hef x hxe hxf
  have hd := segment_direction_of_local_line_at_interior _ _ x d hpo U hU hxU
    (fun z hz hs => hlineP z hz (P.inside i hi hs))
  have hk := segment_direction_of_local_line_at_interior _ _ x k hqo U hU hxU
    (fun z hz hs => hlineQ z hz (Q.inside j hj hs))
  exact det2_ne_zero_of_parallel_nonzero d k _ _ hdk
    (P.minimum_piece_ne_zero hP i hi) (Q.minimum_piece_ne_zero hQ j hj) hd hk

end Zarankiewicz

end

end OAI
