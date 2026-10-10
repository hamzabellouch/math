import OAI.Combinatorics.CompleteCrossing.Angles
import OAI.Combinatorics.CompleteCrossing.Tracks
import OAI.Combinatorics.Crossing.AffinePathHalves
import OAI.Combinatorics.Crossing.SubdivisionSegments
import Mathlib.Algebra.BigOperators.Fin

namespace OAI

/-! Matching refined crossing pieces and arc directions with truncated angle coordinates. -/

section

noncomputable section
open Set Zarankiewicz
namespace Paper170Geometry
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

theorem normalized_piece_vertex_not_crossing (N : Paper170.NormalizedDrawing graph)
    (e : Edge) (i : ℕ) (hi : i ≤ (N.polygonal e).pieces) :
    (N.polygonal e).vertices i ∉ Paper170.crossingPoints N.toContinuousDrawing := by
  have he := (Paper170.toZarankiewiczParametrization (N.polygonal e)).vertices_at
    (⟨i, by omega⟩ : Fin ((N.polygonal e).pieces+1))
  change (N.polygonal e).vertices i = _ at he
  rw [he]
  exact N.crossings_not_knots e _

theorem normalized_crossing_unique_piece (N : Paper170.NormalizedDrawing graph)
    (e : Edge) (x : Plane) (hx : x ∈ Paper170.crossingPoints N.toContinuousDrawing)
    (hxe : x ∈ Paper170.edgeInterior N.toContinuousDrawing e) :
    ∃!i : Fin (N.polygonal e).pieces,
      x ∈ openSegmentTrace ((N.polygonal e).vertices i.val) ((N.polygonal e).vertices (i.val+1)) := by
  obtain ⟨t, ht, rfl⟩ := hxe
  have hn (i : Fin ((N.polygonal e).pieces+1)) : t ≠ (N.polygonal e).knot i := by
    intro he
    exact N.crossings_not_knots e i (he ▸ hx)
  obtain ⟨i, hi⟩ := parametrization_knot_interval (N.polygonal e) t ht hn
  have hmem : N.edge e t ∈ openSegmentTrace ((N.polygonal e).vertices i.val)
      ((N.polygonal e).vertices (i.val+1)) := by
    rw [← parametrization_open_piece]
    exact ⟨t,hi,rfl⟩
  refine ⟨i,hmem,?_⟩
  intro j hj
  rw [← parametrization_open_piece] at hj
  obtain ⟨s,hs,he⟩ := hj
  have hst : s=t := N.edge_injective e he
  subst s
  apply le_antisymm
  · by_contra h
    have hij : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; exact lt_of_not_ge h
    exact hi.2.not_ge (((N.polygonal e).increasing.monotone hij).trans hs.1.le)
  · by_contra h
    have hji : j.succ ≤ i.castSucc := by change j.val+1 ≤ i.val; exact lt_of_not_ge h
    exact hs.2.not_ge (((N.polygonal e).increasing.monotone hji).trans hi.1.le)

theorem openSegmentTrace_of_mem_segment_avoiding (a b x : Plane) (S : Set Plane)
    (hx : x∈S) (ha : a∉S) (hb : b∉S) (hseg : x∈segment ℝ a b) :
    x∈openSegmentTrace a b := by
  rw [← Path.range_segment] at hseg
  obtain ⟨t,ht⟩ := hseg
  have he : segmentPoint a b t.val=x := by
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  exact ⟨t.val,segment_parameter_strict_of_avoids_endpoints a b x S hx ha hb t.val t.property he,he⟩

theorem minimum_crossing_piece_unique [Fintype Vertex] (N : Paper170.NormalizedDrawing graph)
    (V : VertexTruncation N.toContinuousDrawing) (e : Edge) (x : Plane)
    (hx : x ∈ Paper170.crossingPoints N.toContinuousDrawing)
    (i j : Fin (V.chain e).pieces)
    (hi : x∈segment ℝ ((V.chain e).vertices i.val) ((V.chain e).vertices (i.val+1)))
    (hj : x∈segment ℝ ((V.chain e).vertices j.val) ((V.chain e).vertices (j.val+1))) : i=j := by
  suffices hh : ∀ i j : Fin (V.chain e).pieces, i<j →
      x∈segment ℝ ((V.chain e).vertices i.val) ((V.chain e).vertices (i.val+1)) →
      x∈segment ℝ ((V.chain e).vertices j.val) ((V.chain e).vertices (j.val+1)) → False by
    rcases lt_trichotomy i j with h | h | h
    · exact (hh i j h hi hj).elim
    · exact h
    · exact (hh j i h hj hi).elim
  intro i j hij hi hj
  by_cases he : j.val=i.val+1
  · have hj' : x∈segment ℝ ((V.chain e).vertices (i.val+1)) ((V.chain e).vertices (i.val+2)) := by
      simpa only [he, Nat.add_assoc] using hj
    have hxv := (V.chain e).minimum_adjacent_intersection (V.minimal e) i.val (by omega) hi hj'
    exact minimum_vertices_not_crossing N.toAdmissibleDrawing (normalized_locallyStraight N)
      e (V.chain e) (V.minimal e) (i.val+1) (by omega) (hxv ▸ hx)
  · exact Set.disjoint_left.mp ((V.chain e).minimum_nonadjacent_disjoint (V.minimal e)
      i.val j.val (by change i.val<j.val at hij; omega) j.isLt) hi hj

theorem truncated_crossing_unique_piece [Fintype Vertex] (N : Paper170.NormalizedDrawing graph)
    (V : VertexTruncation N.toContinuousDrawing) (e : Edge) (x : Plane)
    (hx : x ∈ Paper170.crossingPoints N.toContinuousDrawing)
    (hxe : x ∈ Paper170.edgeInterior N.toContinuousDrawing e) :
    ∃!i : Fin (V.pieces e), x∈openSegmentTrace (V.vertices e i.val) (V.vertices e (i.val+1)) := by
  have hxr := crossing_mem_truncated_edge N.toAdmissibleDrawing (normalized_noAdjacent N)
    V.chain V.minimal V.radius V.radius_pos V.weak_short V.piece_clearance e x hx hxe
  obtain ⟨i,hi,hxi⟩ := polygonalArcPath_range_piece (V.vertices e) (V.pieces e)
    (V.pieces_pos e) x hxr
  have hm : x∈openSegmentTrace (V.vertices e i) (V.vertices e (i+1)) :=
    openSegmentTrace_of_mem_segment_avoiding _ _ x (Paper170.crossingPoints N.toContinuousDrawing) hx
      (V.vertices_not_crossing (normalized_noAdjacent N) (normalized_locallyStraight N) e i (by omega))
      (V.vertices_not_crossing (normalized_noAdjacent N) (normalized_locallyStraight N) e (i+1) (by omega)) hxi
  refine ⟨⟨i,hi⟩,hm,?_⟩
  intro j hj
  apply minimum_crossing_piece_unique N V e x hx
  · exact (V.chain e).truncated_piece_subset V.radius V.radius_pos (V.weak_short e).1
      (V.weak_short e).2 j.val j.isLt (openSegmentTrace_subset_segment _ _ hj)
  · exact (V.chain e).truncated_piece_subset V.radius V.radius_pos (V.weak_short e).1
      (V.weak_short e).2 i hi hxi

/-- Every actual polygonal-chain piece is traversed along an increasing affine parameter interval. -/
theorem polygonalArcPath_piece_interval (v : ℕ → Plane) : ∀ n i, i<n →
    ∃a b : unitInterval, a<b ∧ ∀t : unitInterval,
      polygonalArcPath v n (intervalSegment a b t)=segmentPoint (v i) (v (i+1)) t.val
  | 0, i, hi => by omega
  | 1, i, hi => by
    have he : i=0 := by omega
    subst i
    refine ⟨0,1,by norm_num,?_⟩
    intro t
    simp only [polygonalArcPath,intervalSegment_zero_one,Path.segment_apply,
      AffineMap.lineMap_apply_module,segmentPoint]
  | n+2, i, hi => by
    by_cases hprev : i<n+1
    · obtain ⟨a,b,hab,hseg⟩ := polygonalArcPath_piece_interval v (n+1) i hprev
      refine ⟨intervalLeft a,intervalLeft b,intervalLeft_strictMono hab,?_⟩
      intro t
      rw [polygonalArcPath,intervalSegment_left,path_trans_intervalLeft]
      exact hseg t
    · have he : i=n+1 := by omega
      subst i
      refine ⟨intervalRight 0,intervalRight 1,intervalRight_strictMono (by norm_num),?_⟩
      intro t
      rw [polygonalArcPath,intervalSegment_right,path_trans_intervalRight,intervalSegment_zero_one]
      simp only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint]

end Paper170Geometry

end
end

section

noncomputable section
open Set Zarankiewicz
namespace Paper170Geometry
variable {Vertex Edge : Type} [Fintype Vertex] {graph : Paper170.Graph Vertex Edge}

/-- At an actual crossing, the truncated chain and original subdivision point in the same direction. -/
theorem truncated_direction_pos_mul_original (N : Paper170.NormalizedDrawing graph)
    (V : VertexTruncation N.toContinuousDrawing) (e : Edge)
    (i : Fin (V.pieces e)) (k : Fin (N.polygonal e).pieces) (x : Plane)
    (hx : x∈Paper170.crossingPoints N.toContinuousDrawing)
    (hxi : x∈openSegmentTrace (V.vertices e i.val) (V.vertices e (i.val+1)))
    (hxk : x∈openSegmentTrace ((N.polygonal e).vertices k.val) ((N.polygonal e).vertices (k.val+1))) :
    ∃r : ℝ, 0<r ∧ V.vertices e (i.val+1)-V.vertices e i.val =
      r • ((N.polygonal e).vertices (k.val+1)-(N.polygonal e).vertices k.val) := by
  have hfull := (V.chain e).truncated_piece_subset V.radius V.radius_pos
    (V.weak_short e).1 (V.weak_short e).2 i.val i.isLt (openSegmentTrace_subset_segment _ _ hxi)
  have hxfull := minimum_piece_crossing_open N.toAdmissibleDrawing (normalized_locallyStraight N)
    e (V.chain e) (V.minimal e) i.val i.isLt x hx hfull
  obtain ⟨a,b,hab,hseg⟩ := polygonalArcPath_piece_interval (V.chain e).vertices
    (V.chain e).pieces i.val i.isLt
  have hend : N.vertex (graph.src e) ≠ N.vertex (graph.dst e) :=
    fun he => graph.loopless e (N.vertex_injective he)
  have hγseg : ∀t : unitInterval,
      N.edge e (intervalSegment ((N.polygonal e).knot k.castSucc) ((N.polygonal e).knot k.succ) t) =
      Paper170.segmentPoint ((N.polygonal e).vertices k.val) ((N.polygonal e).vertices (k.val+1)) t.val :=
    (Paper170.toZarankiewiczParametrization (N.polygonal e)).segment_formula k
  have hηseg : ∀t : unitInterval, (V.chain e).path (intervalSegment a b t) =
      Paper170.segmentPoint ((V.chain e).vertices i.val) ((V.chain e).vertices (i.val+1)) t.val := hseg
  obtain ⟨r,hr,he⟩ := Paper170.path_segments_direction_of_mem (N.edge e) (V.chain e).path
    (N.edge_injective e) ((V.chain e).minimum_path_injective hend (V.minimal e))
    (drawing_chain_range_eq N.toContinuousDrawing e (V.chain e)).symm
    ((N.polygonal e).knot k.castSucc) ((N.polygonal e).knot k.succ) a b
    ((N.polygonal e).increasing Fin.castSucc_lt_succ) hab
    ((N.polygonal e).vertices k.val) ((N.polygonal e).vertices (k.val+1))
    ((V.chain e).vertices i.val) ((V.chain e).vertices (i.val+1)) hγseg hηseg x hxk hxfull
  refine ⟨(V.chain e).truncatedScale V.radius i.val * r,
    mul_pos ((V.chain e).truncatedScale_pos V.radius V.radius_pos (V.short e).1 (V.short e).2 i.val) hr, ?_⟩
  change trackDirection ((V.chain e).truncatedVertices V.radius) i.val = _
  rw [(V.chain e).truncated_direction V.radius i.val i.isLt]
  change (V.chain e).truncatedScale V.radius i.val •
    ((V.chain e).vertices (i.val+1)-(V.chain e).vertices i.val) = _
  rw [he,smul_smul]

end Paper170Geometry

end
end

section

noncomputable section
open Set Zarankiewicz
namespace Paper170Geometry
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

theorem minimum_first_direction (N : Paper170.NormalizedDrawing graph)
    (V : VertexTruncation N.toContinuousDrawing) (e : Edge) :
    ∃r : ℝ, 0 < r ∧ (V.chain e).vertices 1 - (V.chain e).vertices 0 =
      r • ((N.polygonal e).vertices 1 - (N.polygonal e).vertices 0) := by
  let k : Fin (N.polygonal e).pieces := ⟨0, (N.polygonal e).positive⟩
  obtain ⟨a,b,hab,hseg⟩ := polygonalArcPath_piece_interval (V.chain e).vertices
    (V.chain e).pieces 0 (V.pieces_pos e)
  have hend : N.vertex (graph.src e) ≠ N.vertex (graph.dst e) :=
    fun he => graph.loopless e (N.vertex_injective he)
  apply Paper170.path_segments_direction (N.edge e) (V.chain e).path
    (N.edge_injective e) ((V.chain e).minimum_path_injective hend (V.minimal e))
    (drawing_chain_range_eq N.toContinuousDrawing e (V.chain e)).symm
    ((N.polygonal e).knot k.castSucc) ((N.polygonal e).knot k.succ) a b
    ((N.polygonal e).increasing Fin.castSucc_lt_succ) hab
    ((N.polygonal e).vertices 0) ((N.polygonal e).vertices 1)
    ((V.chain e).vertices 0) ((V.chain e).vertices 1)
    ((Paper170.toZarankiewiczParametrization (N.polygonal e)).segment_formula k)
    hseg 0 0 (by norm_num) (by norm_num)
  simpa [Paper170.segmentPoint] using
    (N.polygonal e).vertices_first.trans (V.chain e).first.symm

theorem minimum_last_direction (N : Paper170.NormalizedDrawing graph)
    (V : VertexTruncation N.toContinuousDrawing) (e : Edge) :
    ∃r : ℝ, 0 < r ∧ (V.chain e).vertices ((V.chain e).pieces-1) -
        (V.chain e).vertices (V.chain e).pieces =
      r • ((N.polygonal e).vertices ((N.polygonal e).pieces-1) -
        (N.polygonal e).vertices (N.polygonal e).pieces) := by
  have hn : 0 < (N.polygonal e).pieces := (N.polygonal e).positive
  have hv : 0 < (V.chain e).pieces := V.pieces_pos e
  let k : Fin (N.polygonal e).pieces := ⟨(N.polygonal e).pieces-1, by omega⟩
  obtain ⟨a,b,hab,hseg⟩ := polygonalArcPath_piece_interval (V.chain e).vertices
    (V.chain e).pieces ((V.chain e).pieces-1) (by omega)
  have hend : N.vertex (graph.src e) ≠ N.vertex (graph.dst e) :=
    fun he => graph.loopless e (N.vertex_injective he)
  have hnk : k.val+1 = (N.polygonal e).pieces := by dsimp [k]; omega
  have hvk : (V.chain e).pieces-1+1 = (V.chain e).pieces := by omega
  have hγseg := (Paper170.toZarankiewiczParametrization (N.polygonal e)).segment_formula k
  change ∀t, N.edge e (intervalSegment ((N.polygonal e).knot k.castSucc)
    ((N.polygonal e).knot k.succ) t) =
      Paper170.segmentPoint ((N.polygonal e).vertices k.val)
        ((N.polygonal e).vertices (k.val+1)) t.val at hγseg
  rw [hnk] at hγseg
  rw [hvk] at hseg
  exact Paper170.path_final_segments_direction (N.edge e) (V.chain e).path
    (N.edge_injective e) ((V.chain e).minimum_path_injective hend (V.minimal e))
    (drawing_chain_range_eq N.toContinuousDrawing e (V.chain e)).symm
    ((N.polygonal e).knot k.castSucc) ((N.polygonal e).knot k.succ) a b
    ((N.polygonal e).increasing Fin.castSucc_lt_succ) hab
    ((N.polygonal e).vertices k.val) ((N.polygonal e).vertices (N.polygonal e).pieces)
    ((V.chain e).vertices ((V.chain e).pieces-1)) ((V.chain e).vertices (V.chain e).pieces)
    hγseg hseg ((N.polygonal e).vertices_last.trans (V.chain e).last.symm)

/-- The truncation port lies on the positive ray of the original outward spoke. -/
theorem spokePort_pos_mul_outward (N : Paper170.NormalizedDrawing graph)
    (V : VertexTruncation N.toContinuousDrawing) (j : Vertex) (e : IncidentEdges graph j) :
    ∃r : ℝ, 0 < r ∧ V.spokePort j e - N.vertex j = r • Paper170.outwardSpoke N j e.val := by
  by_cases hsrc : j = graph.src e.val
  · obtain ⟨r,hr,he⟩ := minimum_first_direction N V e.val
    have hp := radialPort_parameter_between ((V.chain e.val).vertices 0)
      ((V.chain e.val).vertices 1) V.radius V.radius_pos (V.weak_short e.val).1
    refine ⟨(V.radius / Real.sqrt (squaredLength
      ((V.chain e.val).vertices 1 - (V.chain e.val).vertices 0))) * r,
      mul_pos hp.1 hr, ?_⟩
    change drawingSpokePort N.toContinuousDrawing V.chain V.radius j e - N.vertex j = _
    rw [drawingSpokePort, ite_eq_left hsrc, PolygonalChain.startPort]
    have hcenter : N.vertex j = (V.chain e.val).vertices 0 := by
      exact (congrArg N.vertex hsrc).trans (V.chain e.val).first.symm
    rw [hcenter, radialPort_sub, he, smul_smul, Paper170.outwardSpoke, ite_eq_left hsrc.symm]
  · have hdst : j = graph.dst e.val := e.property.resolve_left hsrc
    obtain ⟨r,hr,he⟩ := minimum_last_direction N V e.val
    have hshort : V.radius^2 < squaredLength
        ((V.chain e.val).vertices ((V.chain e.val).pieces-1) -
          (V.chain e.val).vertices (V.chain e.val).pieces) := by
      rw [squaredLength_sub_comm]
      exact (V.weak_short e.val).2
    have hp := radialPort_parameter_between ((V.chain e.val).vertices (V.chain e.val).pieces)
      ((V.chain e.val).vertices ((V.chain e.val).pieces-1)) V.radius V.radius_pos hshort
    refine ⟨(V.radius / Real.sqrt (squaredLength
      ((V.chain e.val).vertices ((V.chain e.val).pieces-1) -
        (V.chain e.val).vertices (V.chain e.val).pieces))) * r, mul_pos hp.1 hr, ?_⟩
    change drawingSpokePort N.toContinuousDrawing V.chain V.radius j e - N.vertex j = _
    rw [drawingSpokePort, ite_eq_right hsrc, PolygonalChain.endPort]
    have hcenter : N.vertex j = (V.chain e.val).vertices (V.chain e.val).pieces := by
      exact (congrArg N.vertex hdst).trans (V.chain e.val).last.symm
    rw [hcenter, radialPort_sub, he, smul_smul, Paper170.outwardSpoke,
      ite_eq_right (Ne.symm hsrc)]

end Paper170Geometry

end
end

section

/-! Circle coordinates chosen with the very same cuts and local orders as the
original normalized drawing. -/
noncomputable section
open Set Zarankiewicz
namespace Paper170Geometry
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

theorem exists_truncatedSpokeCoordinates_compatible (N : Paper170.NormalizedDrawing graph)
    (V : VertexTruncation N.toContinuousDrawing) (O : Paper170.SpokeOrders N) :
    ∃C : TruncatedSpokeCoordinates V, ∀j (e f : IncidentEdges graph j),
      orderSign (C.node j e) (C.node j f) = Paper170.spokeComparison O j e.val f.val := by
  classical
  let p (j : Vertex) (e : IncidentEdges graph j) : Plane :=
    V.radius⁻¹ • (V.spokePort j e-N.vertex j)
  have hinc (j : Vertex) (e : IncidentEdges graph j) :
      graph.src e.val=j ∨ graph.dst e.val=j := e.property.imp Eq.symm Eq.symm
  have hp (j : Vertex) (e : IncidentEdges graph j) : Paper170.squaredLength (p j e)=1 := by
    change squaredLength (V.radius⁻¹ • (V.spokePort j e-N.vertex j))=1
    rw [squaredLength_smul,V.spokePort_circle,inv_pow,
      inv_mul_cancel₀ (pow_ne_zero 2 V.radius_pos.ne')]
  have hangle (j : Vertex) (e : IncidentEdges graph j) :
      Paper170.spokeAngle (O.cut j) (p j e)=
        Paper170.spokeAngle (O.cut j) (Paper170.outwardSpoke N j e.val) := by
    dsimp only [p]
    rw [Paper170.spokeAngle_smul _ _ (inv_pos.mpr V.radius_pos)]
    obtain ⟨r,hr,he⟩ := spokePort_pos_mul_outward N V j e
    rw [he,Paper170.spokeAngle_smul _ _ hr]
  have hex (j : Vertex) (e : IncidentEdges graph j) :
      ∃t : ℝ, circlePoint t=Paper170.angleRotation (O.cut j) (p j e) := by
    apply Paper170.angleRotation_parameter _ _ (hp j e)
    rw [hangle]
    exact O.cut_avoids j ⟨e.val,hinc j e⟩
  choose node hnode using hex
  have hpoint (j : Vertex) (e : IncidentEdges graph j) :
      similarityPoint (N.vertex j) (Paper170.angleCoordinateFrame (O.cut j) V.radius)
        (circlePoint (node j e))=V.spokePort j e := by
    rw [hnode]
    exact Paper170.angleCoordinateFrame_point _ _ V.radius_pos _ _
  let C : TruncatedSpokeCoordinates V := {
    frame := fun j => Paper170.angleCoordinateFrame (O.cut j) V.radius
    frame_ne_zero := fun j => Paper170.angleCoordinateFrame_ne_zero _ _ V.radius_pos
    frame_length := fun j => Paper170.angleCoordinateFrame_length (O.cut j) V.radius
    node := node
    node_injective := by
      intro j e f he
      apply V.spokePort_injective (normalized_noAdjacent N) j
      rw [← hpoint j e,← hpoint j f,he]
    point_eq := hpoint }
  refine ⟨C,?_⟩
  have harg (j : Vertex) (e : IncidentEdges graph j) :
      Paper170.spokeAngle (O.cut j) (Paper170.outwardSpoke N j e.val) =
        Complex.arg (Paper170.complexPoint (circlePoint (node j e))) := by
    rw [hnode,Paper170.angleRotation_complex]
    exact (hangle j e).symm
  have hlt (j : Vertex) (e f : IncidentEdges graph j) :
      @LT.lt _ (O.order j).toLT ⟨e.val,hinc j e⟩ ⟨f.val,hinc j f⟩ ↔ node j e < node j f := by
    rw [O.compatible,harg j e,harg j f,Paper170.circlePoint_arg_lt]
  intro j e f
  change orderSign (node j e) (node j f)=_
  unfold Paper170.spokeComparison
  rw [dite_eq_left (hinc j e),dite_eq_left (hinc j f)]
  simp only [orderSign,hlt]

end Paper170Geometry

end
end

section

noncomputable section
open Set Zarankiewicz
open scoped BigOperators
namespace Paper170Geometry
variable {Vertex Edge : Type} [Fintype Vertex] {graph : Paper170.Graph Vertex Edge}

/-- The only remaining geometric input is equality of the local oriented crossing signs. -/
theorem signedIntersection_eq_of_matching_signs (N : Paper170.NormalizedDrawing graph)
    (V : VertexTruncation N.toContinuousDrawing) (e f : Edge) (hef : e≠f)
    (hmatch : ∀ (i : Fin (V.pieces e)) (j : Fin (V.pieces f))
      (k : Fin (N.polygonal e).pieces) (l : Fin (N.polygonal f).pieces) (x : Plane),
      x∈openSegmentTrace (V.vertices e i.val) (V.vertices e (i.val+1)) →
      x∈openSegmentTrace (V.vertices f j.val) (V.vertices f (j.val+1)) →
      x∈openSegmentTrace ((N.polygonal e).vertices k.val) ((N.polygonal e).vertices (k.val+1)) →
      x∈openSegmentTrace ((N.polygonal f).vertices l.val) ((N.polygonal f).vertices (l.val+1)) →
      segmentCrossingSign (V.vertices e i.val) (V.vertices e (i.val+1))
        (V.vertices f j.val) (V.vertices f (j.val+1)) =
      segmentCrossingSign ((N.polygonal e).vertices k.val) ((N.polygonal e).vertices (k.val+1))
        ((N.polygonal f).vertices l.val) ((N.polygonal f).vertices (l.val+1))) :
    V.signedIntersection e f=Paper170.interiorIntersection N e f := by
  classical
  let A := Fin (V.pieces e) × Fin (V.pieces f)
  let B := Fin (N.polygonal e).pieces × Fin (N.polygonal f).pieces
  let F : A → ℝ := fun a => segmentCrossingSign
    (V.vertices e a.1.val) (V.vertices e (a.1.val+1))
    (V.vertices f a.2.val) (V.vertices f (a.2.val+1))
  let G : B → ℝ := fun b => segmentCrossingSign
    ((N.polygonal e).vertices b.1.val) ((N.polygonal e).vertices (b.1.val+1))
    ((N.polygonal f).vertices b.2.val) ((N.polygonal f).vertices (b.2.val+1))
  let R : A → B → Prop := fun a b => ∃x : Plane,
    x∈openSegmentTrace (V.vertices e a.1.val) (V.vertices e (a.1.val+1)) ∧
    x∈openSegmentTrace (V.vertices f a.2.val) (V.vertices f (a.2.val+1)) ∧
    x∈openSegmentTrace ((N.polygonal e).vertices b.1.val) ((N.polygonal e).vertices (b.1.val+1)) ∧
    x∈openSegmentTrace ((N.polygonal f).vertices b.2.val) ((N.polygonal f).vertices (b.2.val+1))
  have hsame (a : A) (b : B) (h : R a b) : F a=G b := by
    obtain ⟨x,hx₁,hx₂,hx₃,hx₄⟩ := h
    exact hmatch a.1 a.2 b.1 b.2 x hx₁ hx₂ hx₃ hx₄
  have hF : ∀a, F a≠0 → ∃!b, G b≠0 ∧ R a b := by
    intro a ha
    have hproper := (segmentCrossingSign_ne_zero_iff _ _ _ _).mp ha
    obtain ⟨s,hs,t,ht,he⟩ := hproper.2
    let x := segmentPoint (V.vertices e a.1.val) (V.vertices e (a.1.val+1)) s
    have hx₁ : x∈openSegmentTrace (V.vertices e a.1.val) (V.vertices e (a.1.val+1)) := ⟨s,hs,rfl⟩
    have hx₂ : x∈openSegmentTrace (V.vertices f a.2.val) (V.vertices f (a.2.val+1)) := ⟨t,ht,he.symm⟩
    have hxe := V.range_subset_edgeInterior e (V.piece_subset_range e a.1.val a.1.isLt
      (openSegmentTrace_subset_segment _ _ hx₁))
    have hxf := V.range_subset_edgeInterior f (V.piece_subset_range f a.2.val a.2.isLt
      (openSegmentTrace_subset_segment _ _ hx₂))
    have hx : x∈Paper170.crossingPoints N.toContinuousDrawing := ⟨e,f,hef,hxe,hxf⟩
    obtain ⟨i,hi,hu⟩ := normalized_crossing_unique_piece N e x hx hxe
    obtain ⟨j,hj,hv⟩ := normalized_crossing_unique_piece N f x hx hxf
    have hR : R a (i,j) := ⟨x,hx₁,hx₂,hi,hj⟩
    refine ⟨(i,j),⟨?_,hR⟩,?_⟩
    · rwa [← hsame a (i,j) hR]
    · rintro b ⟨_,y,hy₁,hy₂,hy₃,hy₄⟩
      have hyx : y=x := openSegments_inter_subsingleton _ _ _ _ hproper.1 ⟨hy₁,hy₂⟩ ⟨hx₁,hx₂⟩
      subst y
      exact Prod.ext (hu b.1 hy₃) (hv b.2 hy₄)
  have hG : ∀b, G b≠0 → ∃!a, F a≠0 ∧ R a b := by
    intro b hb
    have hproper := (segmentCrossingSign_ne_zero_iff _ _ _ _).mp hb
    obtain ⟨s,hs,t,ht,he⟩ := hproper.2
    let x := segmentPoint ((N.polygonal e).vertices b.1.val) ((N.polygonal e).vertices (b.1.val+1)) s
    have hx₃ : x∈openSegmentTrace ((N.polygonal e).vertices b.1.val)
        ((N.polygonal e).vertices (b.1.val+1)) := ⟨s,hs,rfl⟩
    have hx₄ : x∈openSegmentTrace ((N.polygonal f).vertices b.2.val)
        ((N.polygonal f).vertices (b.2.val+1)) := ⟨t,ht,he.symm⟩
    have hxe : x∈Paper170.edgeInterior N.toContinuousDrawing e :=
      (N.polygonal e).segment_mem_interior N.toContinuousDrawing e b.1 s hs
    have hxf : x∈Paper170.edgeInterior N.toContinuousDrawing f := by
      rw [show x=segmentPoint ((N.polygonal f).vertices b.2.val)
        ((N.polygonal f).vertices (b.2.val+1)) t from he]
      exact (N.polygonal f).segment_mem_interior N.toContinuousDrawing f b.2 t ht
    have hx : x∈Paper170.crossingPoints N.toContinuousDrawing := ⟨e,f,hef,hxe,hxf⟩
    obtain ⟨i,hi,hu⟩ := truncated_crossing_unique_piece N V e x hx hxe
    obtain ⟨j,hj,hv⟩ := truncated_crossing_unique_piece N V f x hx hxf
    have hR : R (i,j) b := ⟨x,hi,hj,hx₃,hx₄⟩
    refine ⟨(i,j),⟨?_,hR⟩,?_⟩
    · rwa [hsame (i,j) b hR]
    · rintro a ⟨_,y,hy₁,hy₂,hy₃,hy₄⟩
      have hyx : y=x := openSegments_inter_subsingleton _ _ _ _ hproper.1 ⟨hy₃,hy₄⟩ ⟨hx₃,hx₄⟩
      subst y
      exact Prod.ext (hu a.1 hy₁) (hv a.2 hy₂)
  have hsum : ∑a, F a = ∑b, G b :=
    sum_eq_sum_of_unique_match F G R hF hG (fun a b _ _ h => hsame a b h)
  rw [VertexTruncation.signedIntersection,ite_eq_right hef,Paper170.interiorIntersection,ite_eq_right hef]
  dsimp only [A,B,F,G] at hsum
  simp only [Fintype.sum_prod_type] at hsum
  simp only [Paper170.segmentIntersection_eq_segmentCrossingSign]
  change polygonIntersection (V.vertices e) (V.vertices f) (V.pieces e) (V.pieces f) =
    polygonIntersection (N.polygonal e).vertices (N.polygonal f).vertices
      (N.polygonal e).pieces (N.polygonal f).pieces
  simpa only [polygonIntersection_eq_fin_sum] using hsum

end Paper170Geometry

end
end

section

/-! The cycle engine computes the signed intersection of the original, arbitrary
normalized subdivision, independently of the minimal-chain presentation. -/
noncomputable section
open Set Zarankiewicz
namespace Paper170Geometry.VertexTruncation
variable {Vertex Edge : Type} [Fintype Vertex] {graph : Paper170.Graph Vertex Edge}

theorem signedIntersection_eq_interiorIntersection (N : Paper170.NormalizedDrawing graph)
    (V : VertexTruncation N.toContinuousDrawing) (e f : Edge) :
    V.signedIntersection e f = Paper170.interiorIntersection N e f := by
  classical
  by_cases hef : e=f
  · subst f
    rw [V.signedIntersection_self]
    simp [Paper170.interiorIntersection]
  · apply signedIntersection_eq_of_matching_signs N V e f hef
    intro i j k l x hxi hxj hxk hxl
    have hxe := V.range_subset_edgeInterior e (V.piece_subset_range e i.val i.isLt
      (openSegmentTrace_subset_segment _ _ hxi))
    have hxf := V.range_subset_edgeInterior f (V.piece_subset_range f j.val j.isLt
      (openSegmentTrace_subset_segment _ _ hxj))
    have hx : x∈Paper170.crossingPoints N.toContinuousDrawing := ⟨e,f,hef,hxe,hxf⟩
    obtain ⟨r,hr,he⟩ := truncated_direction_pos_mul_original N V e i k x hx hxi hxk
    obtain ⟨s,hs,hf⟩ := truncated_direction_pos_mul_original N V f j l x hx hxj hxl
    exact segmentCrossingSign_eq_of_pos_directions _ _ _ _ _ _ _ _ x r s hr hs he hf hxi hxj hxk hxl

end Paper170Geometry.VertexTruncation

end
end

end OAI
