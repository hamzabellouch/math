import OAI.Combinatorics.CompleteCrossing.SpokePorts
import OAI.Combinatorics.Crossing.PolygonalParametrizationCover
import OAI.Combinatorics.Crossing.ReducedCrossingCorners
import OAI.Combinatorics.Crossing.ReducedCrossingTransversality
import OAI.Combinatorics.Crossing.TruncatedCrossingCorners
import OAI.Combinatorics.Crossing.TruncatedCrossingRetention
import OAI.Combinatorics.Crossing.TruncatedDrawingDisks
import OAI.Combinatorics.Crossing.TruncatedDrawingInteriors
import OAI.Combinatorics.Crossing.TruncatedSegmentTransversality
import OAI.Combinatorics.Crossing.TruncatedTraceDecomposition
import OAI.Combinatorics.Crossing.VertexDisksCrossingFree
import OAI.Combinatorics.Crossing.VertexTruncation
import OAI.Combinatorics.Crossing.VertexTruncationGeometry

namespace OAI

/-! Vertex-disk truncation, retained crossings, reduced corners, and transverse segments. -/

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} [Fintype Vertex] {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem LocallyStraightAt.exists_trace_line (D : Paper170.ContinuousDrawing graph)
    (e : Edge) (x : Plane) (hx : x ∈ Paper170.edgeInterior D e)
    (h : LocallyStraightAt D e x) :
    ∃ d : Plane, d ≠ 0 ∧ ∃ U : Set Plane, IsOpen U ∧ x ∈ U ∧
      ∀ z ∈ U, z ∈ Set.range (D.edge e) → det2 d (z-x)=0 := by
  obtain ⟨a,b,hab,hxab,U,hU,hxU,htrace⟩ := h.exists_line
  let V : Set Plane := Set.range D.vertex
  have hV : IsClosed V := (Set.finite_range D.vertex).isClosed
  have hxV : x ∉ V := by
    rintro ⟨j,hj⟩
    exact edgeInterior_not_vertex D e x hx j hj.symm
  refine ⟨b-a,sub_ne_zero.mpr (Ne.symm hab),U ∩ Vᶜ,hU.inter hV.isOpen_compl,⟨hxU,hxV⟩,?_⟩
  intro z hz hze
  have hzi : z ∈ Paper170.edgeInterior D e := edgeInterior_of_range_not_vertices D e z hze (by
    intro j hj
    exact hz.2 ⟨j,hj.symm⟩)
  exact det2_of_common_openSegment a b x z hxab ((htrace z hz.1).mp hzi)

theorem minimum_bend_not_locallyStraight (D : Paper170.ContinuousDrawing graph)
    (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e)))
      (D.vertex ((graph.dst e))), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i+2 ≤ P.pieces) (hx : P.vertices (i+1) ∈ Paper170.edgeInterior D e) :
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

theorem minimum_bend_not_crossing (D : Paper170.AdmissibleDrawing graph)
    (hstraight : LocallyStraightCrossings D) (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e)))
      (D.vertex ((graph.dst e))), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i+2 ≤ P.pieces) : P.vertices (i+1) ∉ Paper170.crossingPoints D.toContinuousDrawing := by
  rintro ⟨f,g,hfg,hf,hg⟩
  have hx : P.vertices (i+1) ∈ Paper170.edgeInterior D.toContinuousDrawing e :=
    edgeInterior_of_range_not_vertices D.toContinuousDrawing e _ (P.vertex_mem (i+1) (by omega))
      (edgeInterior_not_vertex D.toContinuousDrawing f _ hf)
  apply minimum_bend_not_locallyStraight D.toContinuousDrawing e P hmin i hi hx
  by_cases hef : e=f
  · subst f
    exact (hstraight.at_crossing e g hfg _ hx hg).1
  · exact (hstraight.at_crossing e f hef _ hx hf).1

theorem minimum_vertices_not_crossing (D : Paper170.AdmissibleDrawing graph)
    (hstraight : LocallyStraightCrossings D) (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e)))
      (D.vertex ((graph.dst e))), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i ≤ P.pieces) : P.vertices i ∉ Paper170.crossingPoints D.toContinuousDrawing := by
  by_cases h0 : i=0
  · subst i
    rw [P.first]
    rintro ⟨f,g,hfg,hf,hg⟩
    exact edgeInterior_not_vertex D.toContinuousDrawing f _ hf ((graph.src e)) rfl
  by_cases hn : i=P.pieces
  · subst i
    rw [P.last]
    rintro ⟨f,g,hfg,hf,hg⟩
    exact edgeInterior_not_vertex D.toContinuousDrawing f _ hf ((graph.dst e)) rfl
  have h := minimum_bend_not_crossing D hstraight e P hmin (i-1) (by omega)
  simpa only [show i-1+1=i by omega] using h

theorem minimum_piece_crossing_open (D : Paper170.AdmissibleDrawing graph)
    (hstraight : LocallyStraightCrossings D) (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ Q : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e)))
      (D.vertex ((graph.dst e))), P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i < P.pieces) (x : Plane) (hx : x ∈ Paper170.crossingPoints D.toContinuousDrawing)
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

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem truncated_piece_vertex_disk_cases (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, 4*r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      4*r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (j : Vertex) (e : Edge) (i : Fin (P e).pieces) (x : Plane)
    (hx : x ∈ segment ℝ ((P e).truncatedVertices r i.val) ((P e).truncatedVertices r (i.val+1))) :
    (j=(graph.src e) ∧ x=(P e).startPort r) ∨
      (j=(graph.dst e) ∧ x=(P e).endPort r) ∨ r^2 < squaredLength (x-D.vertex j) := by
  have hp := drawing_chain_pieces_pos D e (P e)
  by_cases hfirst : j=(graph.src e) ∧ i.val=0
  · have hh := (P e).truncated_first_exterior (hmin e) hp r hr (hshort e).1 (hshort e).2
      (by simpa only [hfirst.2] using hx)
    rcases Set.mem_insert_iff.mp hh with he | he
    · exact Or.inl ⟨hfirst.1,he⟩
    · right; right
      simpa only [Set.mem_ofPred_eq,(P e).first,hfirst.1] using he
  by_cases hlast : j=(graph.dst e) ∧ i.val+1=(P e).pieces
  · have hi : i.val=(P e).pieces-1 := by omega
    have hh := (P e).truncated_last_exterior (hmin e) hp r hr (hshort e).1 (hshort e).2
      (by simpa only [hi,show (P e).pieces-1+1=(P e).pieces by omega] using hx)
    rcases Set.mem_insert_iff.mp hh with he | he
    · exact Or.inr (Or.inl ⟨hlast.1,he⟩)
    · right; right
      simpa only [Set.mem_ofPred_eq,(P e).last,hlast.1] using he
  · right; right
    have hs : r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) := by nlinarith [(hshort e).1,sq_nonneg r]
    have ht : r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)) := by
      nlinarith [(hshort e).2,sq_nonneg r]
    have hxi := (P e).truncated_piece_subset r hr hs ht i.val i.isLt hx
    by_contra h
    exact Set.disjoint_left.mp (hclear j e i (fun h => h.elim hfirst hlast)) (le_of_not_gt h) hxi

theorem truncated_path_vertex_disk_cases (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, 4*r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      4*r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (j : Vertex) (e : Edge) (x : Plane)
    (hx : x ∈ Set.range (polygonalArcPath ((P e).truncatedVertices r) (P e).pieces)) :
    (j=(graph.src e) ∧ x=(P e).startPort r) ∨
      (j=(graph.dst e) ∧ x=(P e).endPort r) ∨ r^2 < squaredLength (x-D.vertex j) := by
  obtain ⟨i,hi,hxi⟩ := polygonalArcPath_range_piece ((P e).truncatedVertices r) (P e).pieces
    (drawing_chain_pieces_pos D e (P e)) x hx
  exact truncated_piece_vertex_disk_cases D P hmin r hr hshort hclear j e ⟨i,hi⟩ x hxi

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} [Fintype Vertex] {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem LocallyTransverseCrossings.exists_trace_lines (D : Paper170.AdmissibleDrawing graph)
    (h : LocallyTransverseCrossings D) (e f : Edge) (hef : e ≠ f)
    (x : Plane) (hxe : x ∈ Paper170.edgeInterior D.toContinuousDrawing e)
    (hxf : x ∈ Paper170.edgeInterior D.toContinuousDrawing f) :
    ∃ d k : Plane, det2 d k ≠ 0 ∧ ∃ U : Set Plane, IsOpen U ∧ x ∈ U ∧
      (∀ z ∈ U, z ∈ Set.range (D.edge e) → det2 d (z-x)=0) ∧
      (∀ z ∈ U, z ∈ Set.range (D.edge f) → det2 k (z-x)=0) := by
  obtain ⟨a,b,c,d,hdet,hxab,hxcd,U,hU,hxU,htraceE,htraceF⟩ := h.at_crossing e f hef x hxe hxf
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

theorem minimum_piece_det_at_crossing (D : Paper170.AdmissibleDrawing graph)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (e f : Edge) (hef : e ≠ f)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (Q : PolygonalChain (Set.range (D.edge f)) (D.vertex ((graph.src f))) (D.vertex ((graph.dst f))))
    (hP : ∀ R : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e)))
      (D.vertex ((graph.dst e))), P.pieces ≤ R.pieces)
    (hQ : ∀ R : PolygonalChain (Set.range (D.edge f)) (D.vertex ((graph.src f)))
      (D.vertex ((graph.dst f))), Q.pieces ≤ R.pieces)
    (i j : ℕ) (hi : i < P.pieces) (hj : j < Q.pieces) (x : Plane)
    (hxe : x ∈ Paper170.edgeInterior D.toContinuousDrawing e) (hxf : x ∈ Paper170.edgeInterior D.toContinuousDrawing f)
    (hxp : x ∈ segment ℝ (P.vertices i) (P.vertices (i+1)))
    (hxq : x ∈ segment ℝ (Q.vertices j) (Q.vertices (j+1))) :
    det2 (P.vertices (i+1)-P.vertices i) (Q.vertices (j+1)-Q.vertices j) ≠ 0 := by
  have hx : x ∈ Paper170.crossingPoints D.toContinuousDrawing := ⟨e,f,hef,hxe,hxf⟩
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

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem drawing_edge_trace_decomposition (D : Paper170.ContinuousDrawing graph)
    (e : Edge)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (r : ℝ) (hr : 0 < r)
    (hfirst : r^2 < squaredLength (P.vertices 1-P.vertices 0))
    (hlast : r^2 < squaredLength (P.vertices P.pieces-P.vertices (P.pieces-1))) :
    Set.range (D.edge e)=
      segment ℝ (D.vertex ((graph.src e))) (P.startPort r) ∪
        Set.range (polygonalArcPath (P.truncatedVertices r) P.pieces) ∪
        segment ℝ (P.endPort r) (D.vertex ((graph.dst e))) := by
  have hp := drawing_chain_pieces_pos D e P
  have hs : segment ℝ (D.vertex ((graph.src e))) (P.startPort r) ⊆ Set.range (D.edge e) := by
    have hx := openSegmentTrace_subset_segment _ _ (radialPort_mem_openSegment (P.vertices 0) (P.vertices 1) r hr hfirst)
    have hh := ((convex_segment (𝕜 := ℝ) _ _).segment_subset (left_mem_segment ℝ _ _) hx).trans (P.inside 0 hp)
    simpa only [PolygonalChain.startPort,P.first] using hh
  have ht : segment ℝ (P.endPort r) (D.vertex ((graph.dst e))) ⊆ Set.range (D.edge e) := by
    have hlen : r^2 < squaredLength (P.vertices (P.pieces-1)-P.vertices P.pieces) := by
      rwa [squaredLength_sub_comm]
    have hx := openSegmentTrace_subset_segment _ _
      (openSegmentTrace_reverse_mem _ _ _ (radialPort_mem_openSegment _ _ r hr hlen))
    have hinside := P.inside (P.pieces-1) (by omega)
    rw [show P.pieces-1+1=P.pieces by omega] at hinside
    have hh := ((convex_segment (𝕜 := ℝ) _ _).segment_subset hx (right_mem_segment ℝ _ _)).trans hinside
    simpa only [PolygonalChain.endPort,P.last] using hh
  let T := P.truncated hp r hr hfirst hlast
  let G := ((Path.segment (D.vertex ((graph.src e))) (P.startPort r)).trans T.path).trans
    (Path.segment (P.endPort r) (D.vertex ((graph.dst e))))
  have hG : Set.range G ⊆ Set.range (D.edge e) := by
    dsimp [G]
    rw [Path.trans_range,Path.trans_range,Path.range_segment,Path.range_segment]
    exact Set.union_subset (Set.union_subset hs T.path_range_subset) ht
  have he := path_range_eq_of_subset (D.edge e) G (D.edge_injective e) hG
  calc
    Set.range (D.edge e) = Set.range G := he.symm
    _ = _ := by
      dsimp [G]
      rw [Path.trans_range,Path.trans_range,Path.range_segment,Path.range_segment]
      rfl

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem vertex_disks_crossing_free (D : Paper170.AdmissibleDrawing graph) (hnorm : NoAdjacentCrossings D)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (r : ℝ)
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (j : Vertex) :
    Disjoint (closedRoundDisk (D.vertex j) r) (Paper170.crossingPoints D.toContinuousDrawing) := by
  apply Set.disjoint_left.mpr
  rintro x hxd ⟨e,f,hef,hxe,hxf⟩
  have hincident (g : Edge) (hxg : x ∈ Paper170.edgeInterior D.toContinuousDrawing g) :
      j=(graph.src g) ∨ j=(graph.dst g) := by
    have hx := edgeInterior_subset_range D.toContinuousDrawing g hxg
    rw [← drawing_chain_range_eq D.toContinuousDrawing g (P g)] at hx
    obtain ⟨i,hi,hxi⟩ := polygonalArcPath_range_piece (P g).vertices (P g).pieces
      (drawing_chain_pieces_pos D.toContinuousDrawing g (P g)) x hx
    by_contra h
    have hbad : ¬ ((j=(graph.src g) ∧ i=0) ∨ (j=(graph.dst g) ∧ i+1=(P g).pieces)) :=
      fun hh => h (hh.elim (fun hh => Or.inl hh.1) (fun hh => Or.inr hh.1))
    exact Set.disjoint_left.mp (hclear j g ⟨i,hi⟩ hbad) hxd hxi
  have hadj := incident_edges_adjacent j ⟨e,hincident e hxe⟩ ⟨f,hincident f hxf⟩
  have hh : x ∈ Paper170.edgeInterior D.toContinuousDrawing e ∩ Paper170.edgeInterior D.toContinuousDrawing f := ⟨hxe,hxf⟩
  rw [hnorm.eq_empty e f hef hadj] at hh
  exact hh

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem crossing_mem_truncated_edge (D : Paper170.AdmissibleDrawing graph) (hnorm : NoAdjacentCrossings D)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (e : Edge) (x : Plane) (hx : x ∈ Paper170.crossingPoints D.toContinuousDrawing)
    (hxe : x ∈ Paper170.edgeInterior D.toContinuousDrawing e) :
    x ∈ Set.range (polygonalArcPath ((P e).truncatedVertices r) (P e).pieces) := by
  have hh := edgeInterior_subset_range D.toContinuousDrawing e hxe
  rw [drawing_edge_trace_decomposition D.toContinuousDrawing e (P e) r hr (hshort e).1 (hshort e).2] at hh
  rcases hh with (hs | hm) | ht
  · have hmem := center_segment_in_disk (D.vertex ((graph.src e))) ((P e).startPort r) r
      (drawing_chain_startPort_circle D.toContinuousDrawing e (P e) (hmin e) r) hs
    exact False.elim (Set.disjoint_left.mp (vertex_disks_crossing_free D hnorm P r hclear ((graph.src e))) hmem hx)
  · exact hm
  · have ht' : x ∈ segment ℝ (D.vertex ((graph.dst e))) ((P e).endPort r) := by
      simpa only [segment_symm ℝ ((P e).endPort r) (D.vertex ((graph.dst e)))] using ht
    have hmem := center_segment_in_disk (D.vertex ((graph.dst e))) ((P e).endPort r) r
      (drawing_chain_endPort_circle D.toContinuousDrawing e (P e) (hmin e) r) ht'
    exact False.elim (Set.disjoint_left.mp (vertex_disks_crossing_free D hnorm P r hclear ((graph.dst e))) hmem hx)

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem truncated_range_subset_edgeInterior (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, 4*r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      4*r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (e : Edge) :
    Set.range (polygonalArcPath ((P e).truncatedVertices r) (P e).pieces) ⊆ Paper170.edgeInterior D e := by
  intro x hx
  have hs : r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) := by nlinarith [(hshort e).1,sq_nonneg r]
  have ht : r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)) := by
    nlinarith [(hshort e).2,sq_nonneg r]
  apply edgeInterior_of_range_not_vertices D e x
  · exact ((P e).truncated (drawing_chain_pieces_pos D e (P e)) r hr hs ht).path_range_subset hx
  · intro j he
    rcases truncated_path_vertex_disk_cases D P hmin r hr hshort hclear j e x hx with ⟨hj,hp⟩ | ⟨hj,hp⟩ | hout
    · have hpi := drawing_chain_startPort_interior D e (P e) (hmin e) r hr hs
      exact edgeInterior_not_vertex D e _ hpi j (hp.symm.trans he)
    · have hpi := drawing_chain_endPort_interior D e (P e) (hmin e) r hr ht
      exact edgeInterior_not_vertex D e _ hpi j (hp.symm.trans he)
    · rw [he,sub_self] at hout
      have hz : squaredLength (0 : Plane)=0 := by simp [squaredLength]
      rw [hz] at hout
      exact (sq_nonneg r).not_gt hout

theorem truncated_edge_intersections_eq (D : Paper170.AdmissibleDrawing graph) (hnorm : NoAdjacentCrossings D)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, 4*r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      4*r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (e f : Edge) (hef : e ≠ f) :
    Set.range (polygonalArcPath ((P e).truncatedVertices r) (P e).pieces) ∩
      Set.range (polygonalArcPath ((P f).truncatedVertices r) (P f).pieces) =
      Paper170.edgeInterior D.toContinuousDrawing e ∩ Paper170.edgeInterior D.toContinuousDrawing f := by
  have hweak (g : Edge) :
      r^2 < squaredLength ((P g).vertices 1-(P g).vertices 0) ∧
      r^2 < squaredLength ((P g).vertices (P g).pieces-(P g).vertices ((P g).pieces-1)) := by
    constructor <;> nlinarith [(hshort g).1,(hshort g).2,sq_nonneg r]
  ext x
  constructor
  · rintro ⟨hx,hy⟩
    exact ⟨truncated_range_subset_edgeInterior D.toContinuousDrawing P hmin r hr hshort hclear e hx,
      truncated_range_subset_edgeInterior D.toContinuousDrawing P hmin r hr hshort hclear f hy⟩
  · rintro ⟨hx,hy⟩
    have hc : x ∈ Paper170.crossingPoints D.toContinuousDrawing := ⟨e,f,hef,hx,hy⟩
    exact ⟨crossing_mem_truncated_edge D hnorm P hmin r hr hweak hclear e x hc hx,
      crossing_mem_truncated_edge D hnorm P hmin r hr hweak hclear f x hc hy⟩

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} [Fintype Vertex] {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem truncated_vertices_not_crossing (D : Paper170.AdmissibleDrawing graph)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (r : ℝ)
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (e : Edge) (i : ℕ) (hi : i ≤ (P e).pieces) :
    (P e).truncatedVertices r i ∉ Paper170.crossingPoints D.toContinuousDrawing := by
  by_cases h0 : i=0
  · subst i
    rw [(P e).truncatedVertices_first]
    intro hx
    have hc := (drawing_chain_startPort_circle D.toContinuousDrawing e (P e) (hmin e) r).le
    exact Set.disjoint_left.mp (vertex_disks_crossing_free D hnorm P r hclear ((graph.src e))) hc hx
  by_cases hn : i=(P e).pieces
  · subst i
    rw [(P e).truncatedVertices_last (drawing_chain_pieces_pos D.toContinuousDrawing e (P e))]
    intro hx
    have hc := (drawing_chain_endPort_circle D.toContinuousDrawing e (P e) (hmin e) r).le
    exact Set.disjoint_left.mp (vertex_disks_crossing_free D hnorm P r hclear ((graph.dst e))) hc hx
  · simp only [PolygonalChain.truncatedVertices,ite_eq_right h0,ite_eq_right hn]
    exact minimum_vertices_not_crossing D hstraight e (P e) (hmin e) i hi

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} [Fintype Vertex] {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem truncated_segment_pair_transverse (D : Paper170.AdmissibleDrawing graph)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D)
    (htrans : LocallyTransverseCrossings D)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, 4*r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      4*r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (e f : Edge) (hef : e ≠ f) (i : Fin (P e).pieces) (j : Fin (P f).pieces) :
    SegmentPairTransverse ((P e).truncatedVertices r i.val) ((P e).truncatedVertices r (i.val+1))
      ((P f).truncatedVertices r j.val) ((P f).truncatedVertices r (j.val+1)) := by
  intro s hs t ht he
  let x := segmentPoint ((P e).truncatedVertices r i.val) ((P e).truncatedVertices r (i.val+1)) s
  have hxe : x ∈ segment ℝ ((P e).truncatedVertices r i.val) ((P e).truncatedVertices r (i.val+1)) := by
    rw [← Path.range_segment]
    exact ⟨⟨s,hs⟩,by simp only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint,x]⟩
  have hxf : x ∈ segment ℝ ((P f).truncatedVertices r j.val) ((P f).truncatedVertices r (j.val+1)) := by
    rw [← Path.range_segment]
    refine ⟨⟨t,ht⟩,?_⟩
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,x,segmentPoint] using he.symm
  have hie := truncated_range_subset_edgeInterior D.toContinuousDrawing P hmin r hr hshort hclear e
    (polygonalArcPath_piece_subset_range _ _ i.val i.isLt hxe)
  have hif := truncated_range_subset_edgeInterior D.toContinuousDrawing P hmin r hr hshort hclear f
    (polygonalArcPath_piece_subset_range _ _ j.val j.isLt hxf)
  have hcross : x ∈ Paper170.crossingPoints D.toContinuousDrawing := ⟨e,f,hef,hie,hif⟩
  have hcorner := truncated_vertices_not_crossing D hnorm hstraight P hmin r hclear
  have hsi := segment_parameter_strict_of_avoids_endpoints _ _ x _ hcross
    (hcorner e i.val (by omega)) (hcorner e (i.val+1) (by omega)) s hs rfl
  have hti := segment_parameter_strict_of_avoids_endpoints _ _ x _ hcross
    (hcorner f j.val (by omega)) (hcorner f (j.val+1) (by omega)) t ht he.symm
  refine ⟨?_,hsi,hti⟩
  have hweak (g : Edge) :
      r^2 < squaredLength ((P g).vertices 1-(P g).vertices 0) ∧
      r^2 < squaredLength ((P g).vertices (P g).pieces-(P g).vertices ((P g).pieces-1)) := by
    constructor <;> nlinarith [(hshort g).1,(hshort g).2,sq_nonneg r]
  have hde := minimum_piece_det_at_crossing D hstraight htrans e f hef (P e) (P f) (hmin e) (hmin f)
    i.val j.val i.isLt j.isLt x hie hif
    ((P e).truncated_piece_subset r hr (hweak e).1 (hweak e).2 i.val i.isLt hxe)
    ((P f).truncated_piece_subset r hr (hweak f).1 (hweak f).2 j.val j.isLt hxf)
  change det2 (trackDirection ((P e).truncatedVertices r) i.val) (trackDirection ((P f).truncatedVertices r) j.val) ≠ 0
  rw [(P e).truncated_direction r i.val i.isLt,(P f).truncated_direction r j.val j.isLt,
    det2_smul_left,det2_smul_right]
  exact mul_ne_zero (ne_of_gt ((P e).truncatedScale_pos r hr (hshort e).1 (hshort e).2 i.val))
    (mul_ne_zero (ne_of_gt ((P f).truncatedScale_pos r hr (hshort f).1 (hshort f).2 j.val)) hde)

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
structure VertexTruncation (D : Paper170.ContinuousDrawing graph) where
  chain : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
    (D.vertex ((graph.src e))) (D.vertex ((graph.dst e)))
  minimal : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
    (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (chain e).pieces ≤ Q.pieces
  radius : ℝ
  radius_pos : 0 < radius
  short : ∀ e, 4*radius^2 < squaredLength ((chain e).vertices 1-(chain e).vertices 0) ∧
    4*radius^2 < squaredLength ((chain e).vertices (chain e).pieces-(chain e).vertices ((chain e).pieces-1))
  disks_disjoint : ∀ j k, j ≠ k →
    Disjoint (closedRoundDisk (D.vertex j) radius) (closedRoundDisk (D.vertex k) radius)
  piece_clearance : ∀ j e (i : Fin (chain e).pieces),
    ¬ ((j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=(chain e).pieces)) →
    Disjoint (closedRoundDisk (D.vertex j) radius)
      (segment ℝ ((chain e).vertices i.val) ((chain e).vertices (i.val+1)))

theorem nonempty_vertexTruncation [Fintype Vertex] [Fintype Edge] (D : Paper170.ContinuousDrawing graph)
    (hpoly : ∀ e, HasFiniteAffineCover (D.edge e)) : Nonempty (VertexTruncation D) := by
  classical
  have hex (e : Edge) := exists_reduced_polygonalChain (D.edge e) (D.edge_injective e) (hpoly e)
  choose P htrace hinj hpos hdir hbend hmin using hex
  obtain ⟨ρ,hρ,hdis,hclear⟩ := exists_vertex_piece_clearance D P hmin
  obtain ⟨r,hr,hrρ,hshort⟩ := exists_short_vertex_radius D P hmin ρ hρ
  refine ⟨⟨P,hmin,r,hr,hshort,?_,?_⟩⟩
  · intro j k hjk
    exact (hdis j k hjk).mono (closedRoundDisk_mono _ hr.le hrρ) (closedRoundDisk_mono _ hr.le hrρ)
  · intro j e i hi
    exact (hclear j e i hi).mono_left (closedRoundDisk_mono _ hr.le hrρ)

namespace VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

def pieces (e : Edge) : ℕ := (V.chain e).pieces

def vertices (e : Edge) : ℕ → Plane := (V.chain e).truncatedVertices V.radius

def startPort (e : Edge) : Plane := (V.chain e).startPort V.radius

def endPort (e : Edge) : Plane := (V.chain e).endPort V.radius

theorem pieces_pos (e : Edge) : 0 < V.pieces e := drawing_chain_pieces_pos D e (V.chain e)

theorem weak_short (e : Edge) :
    V.radius^2 < squaredLength ((V.chain e).vertices 1-(V.chain e).vertices 0) ∧
    V.radius^2 < squaredLength ((V.chain e).vertices (V.chain e).pieces-(V.chain e).vertices ((V.chain e).pieces-1)) := by
  constructor <;> nlinarith [(V.short e).1,(V.short e).2,sq_nonneg V.radius]

def path (e : Edge) : Path (V.startPort e) (V.endPort e) :=
  ((V.chain e).truncated (V.pieces_pos e) V.radius V.radius_pos (V.weak_short e).1 (V.weak_short e).2).path

theorem path_injective (e : Edge) : Function.Injective (V.path e) :=
  (V.chain e).truncated_path_injective (V.minimal e) (V.pieces_pos e) V.radius V.radius_pos
    (V.short e).1 (V.short e).2

theorem path_hasFiniteAffineCover (e : Edge) : HasFiniteAffineCover (V.path e) :=
  ((V.chain e).truncated (V.pieces_pos e) V.radius V.radius_pos (V.weak_short e).1 (V.weak_short e).2).hasFiniteAffineCover

theorem range_subset_edgeInterior (e : Edge) : Set.range (V.path e) ⊆ Paper170.edgeInterior D e :=
  truncated_range_subset_edgeInterior D V.chain V.minimal V.radius V.radius_pos V.short V.piece_clearance e

theorem direction_ne_zero (e : Edge) (i : ℕ) (hi : i < V.pieces e) :
    trackDirection (V.vertices e) i ≠ 0 :=
  (V.chain e).truncated_direction_ne_zero (V.minimal e) V.radius V.radius_pos (V.short e).1 (V.short e).2 i hi

end VertexTruncation

end Paper170Geometry

end
end

section

noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.VertexTruncation
theorem offset_avoidance {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D) (e : Edge) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ≠ 0 → |t| < δ → ∀ i j : Fin (V.pieces e),
      ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
        (shiftedTrack (V.vertices e) (V.pieces e) t j.val)
        (shiftedTrack (V.vertices e) (V.pieces e) t (j.val+1)) :=
  (V.chain e).truncated_offset_avoidance (V.minimal e) V.radius V.radius_pos (V.short e).1 (V.short e).2

theorem edge_intersections_eq {D : Paper170.AdmissibleDrawing graph} (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (e f : Edge) (hef : e ≠ f) :
    Set.range (V.path e) ∩ Set.range (V.path f)=Paper170.edgeInterior D.toContinuousDrawing e ∩ Paper170.edgeInterior D.toContinuousDrawing f :=
  truncated_edge_intersections_eq D hnorm V.chain V.minimal V.radius V.radius_pos V.short V.piece_clearance e f hef

theorem pair_transverse [Fintype Vertex] {D : Paper170.AdmissibleDrawing graph} (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (e f : Edge) (hef : e ≠ f) (i : Fin (V.pieces e)) (j : Fin (V.pieces f)) :
    SegmentPairTransverse (V.vertices e i.val) (V.vertices e (i.val+1))
      (V.vertices f j.val) (V.vertices f (j.val+1)) :=
  truncated_segment_pair_transverse D hnorm hstraight htrans V.chain V.minimal V.radius V.radius_pos
    V.short V.piece_clearance e f hef i j

theorem crossing_free_disks {D : Paper170.AdmissibleDrawing graph} (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (j : Vertex) :
    Disjoint (closedRoundDisk (D.vertex j) V.radius) (Paper170.crossingPoints D.toContinuousDrawing) :=
  vertex_disks_crossing_free D hnorm V.chain V.radius V.piece_clearance j

theorem vertices_not_crossing [Fintype Vertex] {D : Paper170.AdmissibleDrawing graph} (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D)
    (e : Edge) (i : ℕ) (hi : i ≤ V.pieces e) : V.vertices e i ∉ Paper170.crossingPoints D.toContinuousDrawing :=
  truncated_vertices_not_crossing D hnorm hstraight V.chain V.minimal V.radius V.piece_clearance e i hi

theorem vertex_disk_cases {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)
    (j : Vertex) (e : Edge) (x : Plane) (hx : x ∈ Set.range (V.path e)) :
    (j=(graph.src e) ∧ x=V.startPort e) ∨ (j=(graph.dst e) ∧ x=V.endPort e) ∨
      V.radius^2 < squaredLength (x-D.vertex j) :=
  truncated_path_vertex_disk_cases D V.chain V.minimal V.radius V.radius_pos V.short V.piece_clearance j e x hx

end Paper170Geometry.VertexTruncation

namespace Paper170Geometry

theorem normalized_vertexTruncation [Fintype Vertex] [Fintype Edge]
    (N : Paper170.NormalizedDrawing graph) : Nonempty (VertexTruncation N.toContinuousDrawing) :=
  nonempty_vertexTruncation N.toContinuousDrawing (fun e =>
    (Paper170.toZarankiewiczParametrization (N.polygonal e)).hasFiniteAffineCover)

end Paper170Geometry

end
end

end OAI
