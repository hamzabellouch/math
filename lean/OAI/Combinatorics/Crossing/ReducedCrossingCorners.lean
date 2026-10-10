import OAI.Combinatorics.Crossing.LocalLineBends
import OAI.Combinatorics.Crossing.ReducedPolygonalPresentation
import OAI.Combinatorics.Crossing.LocallyStraightNormalization
import OAI.Combinatorics.Crossing.DrawingRangeCrossings

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem det2_of_common_openSegment (a b x z : Plane)
    (hx : x ∈ openSegmentTrace a b) (hz : z ∈ openSegmentTrace a b) :
    det2 (b-a) (z-x)=0 := by
  obtain ⟨t,ht,rfl⟩ := hx
  obtain ⟨u,hu,rfl⟩ := hz
  dsimp [det2,segmentPoint]
  ring

theorem LocallyStraightAt.exists_trace_line (D : ContinuousDrawing m n)
    (e : BipartiteEdge m n) (x : Plane) (hx : x ∈ edgeInterior D e)
    (h : LocallyStraightAt D e x) :
    ∃ d : Plane, d ≠ 0 ∧ ∃ U : Set Plane, IsOpen U ∧ x ∈ U ∧
      ∀ z ∈ U, z ∈ Set.range (D.edge e) → det2 d (z-x)=0 := by
  obtain ⟨a,b,hab,hxab,U,hU,hxU,htrace⟩ := h
  let V : Set Plane := Set.range D.vertex
  have hV : IsClosed V := (Set.finite_range D.vertex).isClosed
  have hxV : x ∉ V := by
    rintro ⟨j,hj⟩
    exact edgeInterior_not_vertex D e x hx j hj.symm
  refine ⟨b-a,sub_ne_zero.mpr (Ne.symm hab),U ∩ Vᶜ,hU.inter hV.isOpen_compl,⟨hxU,hxV⟩,?_⟩
  intro z hz hze
  have hzi : z ∈ edgeInterior D e := edgeInterior_of_range_not_vertices D e z hze (by
    intro j hj
    exact hz.2 ⟨j,hj.symm⟩)
  exact det2_of_common_openSegment a b x z hxab ((htrace z hz.1).mp hzi)

theorem minimum_bend_not_locallyStraight (D : ContinuousDrawing m n)
    (e : BipartiteEdge m n)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1))
      (D.vertex (.inr e.2)), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i+2 ≤ P.pieces) (hx : P.vertices (i+1) ∈ edgeInterior D e) :
    ¬ LocallyStraightAt D e (P.vertices (i+1)) := by
  intro h
  obtain ⟨d,hd,U,hU,hxU,hh⟩ := LocallyStraightAt.exists_trace_line D e _ hx h
  apply P.minimum_bend_det_ne_zero hmin i hi
  apply bend_det_zero_of_local_line _ _ _ d hd U hU hxU
  intro z hz hseg
  apply hh z hz
  rcases hseg with hseg | hseg
  · exact P.inside i (by omega) hseg
  · exact P.inside (i+1) (by omega) hseg

theorem minimum_bend_not_crossing (D : AdmissibleDrawing m n)
    (hstraight : LocallyStraightCrossings D) (e : BipartiteEdge m n)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1))
      (D.vertex (.inr e.2)), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i+2 ≤ P.pieces) : P.vertices (i+1) ∉ crossingPoints D.toContinuousDrawing := by
  rintro ⟨f,g,hfg,hf,hg⟩
  have hx : P.vertices (i+1) ∈ edgeInterior D.toContinuousDrawing e :=
    edgeInterior_of_range_not_vertices D.toContinuousDrawing e _ (P.vertex_mem (i+1) (by omega))
      (edgeInterior_not_vertex D.toContinuousDrawing f _ hf)
  apply minimum_bend_not_locallyStraight D.toContinuousDrawing e P hmin i hi hx
  by_cases hef : e=f
  · subst f
    exact (hstraight e g hfg _ hx hg).1
  · exact (hstraight e f hef _ hx hf).1

theorem minimum_vertices_not_crossing (D : AdmissibleDrawing m n)
    (hstraight : LocallyStraightCrossings D) (e : BipartiteEdge m n)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1))
      (D.vertex (.inr e.2)), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i ≤ P.pieces) : P.vertices i ∉ crossingPoints D.toContinuousDrawing := by
  by_cases h0 : i=0
  · subst i
    rw [P.first]
    rintro ⟨f,g,hfg,hf,hg⟩
    exact edgeInterior_not_vertex D.toContinuousDrawing f _ hf (.inl e.1) rfl
  by_cases hn : i=P.pieces
  · subst i
    rw [P.last]
    rintro ⟨f,g,hfg,hf,hg⟩
    exact edgeInterior_not_vertex D.toContinuousDrawing f _ hf (.inr e.2) rfl
  have h := minimum_bend_not_crossing D hstraight e P hmin (i-1) (by omega)
  simpa only [show i-1+1=i by omega] using h

theorem minimum_piece_crossing_open (D : AdmissibleDrawing m n)
    (hstraight : LocallyStraightCrossings D) (e : BipartiteEdge m n)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1))
      (D.vertex (.inr e.2)), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i < P.pieces) (x : Plane) (hx : x ∈ crossingPoints D.toContinuousDrawing)
    (hseg : x ∈ segment ℝ (P.vertices i) (P.vertices (i+1))) :
    x ∈ openSegmentTrace (P.vertices i) (P.vertices (i+1)) := by
  rw [← Path.range_segment] at hseg
  obtain ⟨t,ht⟩ := hseg
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    simp only [Path.source] at ht
    exact minimum_vertices_not_crossing D hstraight e P hmin i (by omega) (ht.symm ▸ hx)
  have ht1 : t ≠ 1 := by
    intro h
    subst t
    simp only [Path.target] at ht
    exact minimum_vertices_not_crossing D hstraight e P hmin (i+1) (by omega) (ht.symm ▸ hx)
  refine ⟨t.val,⟨?_,?_⟩,?_⟩
  · exact lt_of_le_of_ne t.property.1 (fun h => ht0 (Subtype.ext h.symm))
  · exact lt_of_le_of_ne t.property.2 (fun h => ht1 (Subtype.ext h))
  · simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht

end Zarankiewicz

end

end OAI
