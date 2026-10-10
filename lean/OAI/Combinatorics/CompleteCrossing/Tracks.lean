import OAI.Combinatorics.CompleteCrossing.Truncation
import OAI.Combinatorics.Crossing.CircleOffsetLine
import OAI.Combinatorics.Crossing.FiniteMovingPoints
import OAI.Combinatorics.Crossing.PolygonalWalks
import OAI.Combinatorics.Crossing.TangentTrackIdentity

namespace OAI

/-! Truncated spoke coordinates, endpoint connections, and stable signed track intersections. -/

section

/-! Fixed graph-edge directions at both endpoint circles, including the incoming right-vertex direction. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry

def drawingSpokeDirection (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (j : Vertex) (e : IncidentEdges graph j) : Plane :=
  if j=(graph.src e.val) then trackDirection (P e.val).vertices 0
    else trackDirection (P e.val).vertices ((P e.val).pieces-1)

theorem drawingSpokeDirection_ne_zero (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (j : Vertex) (e : IncidentEdges graph j) : drawingSpokeDirection D P j e ≠ 0 := by
  have hp := drawing_chain_pieces_pos D e.val (P e.val)
  unfold drawingSpokeDirection
  split_ifs
  · exact (P e.val).minimum_piece_ne_zero (hmin e.val) 0 hp
  · exact (P e.val).minimum_piece_ne_zero (hmin e.val) ((P e.val).pieces-1) (by omega)

theorem drawingSpokeDirection_port_parallel (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (r : ℝ) (j : Vertex) (e : IncidentEdges graph j)
    (hpos : 0 < (P e.val).pieces) :
    det2 (drawingSpokeDirection D P j e) (drawingSpokePort D P r j e-D.vertex j)=0 := by
  unfold drawingSpokeDirection drawingSpokePort
  split_ifs with h
  · have hc : D.vertex j=(P e.val).vertices 0 := (congrArg D.vertex h).trans (P e.val).first.symm
    rw [hc]
    change det2 ((P e.val).vertices 1-(P e.val).vertices 0)
      (radialPort ((P e.val).vertices 0) ((P e.val).vertices 1) r-(P e.val).vertices 0)=0
    rw [radialPort_sub,det2_smul_right,det2_self,mul_zero]
  · have he := e.property.resolve_left h
    have hc : D.vertex j=(P e.val).vertices (P e.val).pieces :=
      (congrArg D.vertex he).trans (P e.val).last.symm
    rw [hc]
    simp only [trackDirection,PolygonalChain.endPort,
      show (P e.val).pieces-1+1=(P e.val).pieces by omega,radialPort_sub,det2_smul_right]
    have hn : (P e.val).vertices ((P e.val).pieces-1)-(P e.val).vertices (P e.val).pieces =
        -((P e.val).vertices (P e.val).pieces-(P e.val).vertices ((P e.val).pieces-1)) := by abel
    rw [hn,det2_neg_right,det2_self,neg_zero,mul_zero]

theorem drawingSpokeScale_ne_zero (D : Paper170.ContinuousDrawing graph)
    (P : ∀ e : Edge, PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r) (j : Vertex) (e : IncidentEdges graph j) :
    circleTrackScale (drawingSpokeDirection D P j e) (drawingSpokePort D P r j e-D.vertex j) ≠ 0 := by
  have hw : drawingSpokePort D P r j e-D.vertex j ≠ 0 := by
    intro hh
    have hc := drawingSpokePort_circle D P hmin r j e
    rw [hh] at hc
    have hz : squaredLength (0 : Plane)=0 := by simp [squaredLength]
    rw [hz] at hc
    nlinarith
  exact circleTrackScale_ne_zero _ _ (drawingSpokeDirection_ne_zero D P hmin j e) hw
    (drawingSpokeDirection_port_parallel D P r j e (drawing_chain_pieces_pos D e.val (P e.val)))

end Paper170Geometry

end
end

section

/-! The actual endpoint directions of truncated tracks, with their common fixed edge orientation. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

def spokePort (j : Vertex) (e : IncidentEdges graph j) : Plane :=
  drawingSpokePort D V.chain V.radius j e

def spokeIndex (j : Vertex) (e : IncidentEdges graph j) : ℕ :=
  if j=(graph.src e.val) then 0 else V.pieces e.val-1

def spokeDirection (j : Vertex) (e : IncidentEdges graph j) : Plane :=
  trackDirection (V.vertices e.val) (V.spokeIndex j e)

theorem spokeIndex_lt (j : Vertex) (e : IncidentEdges graph j) :
    V.spokeIndex j e < V.pieces e.val := by
  have hp := V.pieces_pos e.val
  unfold spokeIndex
  split_ifs <;> omega

theorem spokeDirection_ne_zero (j : Vertex) (e : IncidentEdges graph j) :
    V.spokeDirection j e ≠ 0 := V.direction_ne_zero e.val _ (V.spokeIndex_lt j e)

theorem spokeDirection_eq_scale (j : Vertex) (e : IncidentEdges graph j) :
    V.spokeDirection j e =
      (V.chain e.val).truncatedScale V.radius (V.spokeIndex j e) •
        drawingSpokeDirection D V.chain j e := by
  change trackDirection ((V.chain e.val).truncatedVertices V.radius) (V.spokeIndex j e)=_
  rw [(V.chain e.val).truncated_direction V.radius _ (V.spokeIndex_lt j e)]
  congr 1
  unfold spokeIndex drawingSpokeDirection
  split_ifs <;> rfl

theorem spokePort_circle (j : Vertex) (e : IncidentEdges graph j) :
    squaredLength (V.spokePort j e-D.vertex j)=V.radius^2 :=
  drawingSpokePort_circle D V.chain V.minimal V.radius j e

theorem spokePort_ne_center (j : Vertex) (e : IncidentEdges graph j) :
    V.spokePort j e-D.vertex j ≠ 0 := by
  intro h
  have hc := V.spokePort_circle j e
  rw [h] at hc
  have hz : squaredLength (0 : Plane)=0 := by simp [squaredLength]
  rw [hz] at hc
  nlinarith [V.radius_pos]

theorem spokeDirection_parallel (j : Vertex) (e : IncidentEdges graph j) :
    det2 (V.spokeDirection j e) (V.spokePort j e-D.vertex j)=0 := by
  rw [V.spokeDirection_eq_scale,det2_smul_left]
  have hp := drawingSpokeDirection_port_parallel D V.chain V.radius j e (V.pieces_pos e.val)
  change det2 (drawingSpokeDirection D V.chain j e) (V.spokePort j e-D.vertex j)=0 at hp
  rw [hp,mul_zero]

def spokeScale (j : Vertex) (e : IncidentEdges graph j) : ℝ :=
  circleTrackScale (V.spokeDirection j e) (V.spokePort j e-D.vertex j)

theorem spokeScale_ne_zero (j : Vertex) (e : IncidentEdges graph j) :
    V.spokeScale j e ≠ 0 :=
  circleTrackScale_ne_zero _ _ (V.spokeDirection_ne_zero j e)
    (V.spokePort_ne_center j e) (V.spokeDirection_parallel j e)

theorem spokePort_injective {A : Paper170.AdmissibleDrawing graph}
    (V : VertexTruncation A.toContinuousDrawing) (hnorm : NoAdjacentCrossings A)
    (j : Vertex) : Function.Injective (V.spokePort j) :=
  drawingSpokePort_injective A hnorm V.chain V.minimal V.radius V.radius_pos V.weak_short j

end Paper170Geometry.VertexTruncation

end
end

section

/-! One perturbation radius preserves every actual distinct-edge segment crossing and its sign. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.VertexTruncation
variable {D : Paper170.AdmissibleDrawing graph}

theorem exists_distinct_edge_shift_radius [Fintype Vertex] [Fintype Edge] (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ e f : Edge, e ≠ f →
      ∀ i : Fin (V.pieces e), ∀ j : Fin (V.pieces f),
        SegmentPairTransverse (V.vertices e i.val) (V.vertices e (i.val+1))
          (shiftedTrack (V.vertices f) (V.pieces f) t j.val)
          (shiftedTrack (V.vertices f) (V.pieces f) t (j.val+1)) ∧
        segmentCrossingSign (V.vertices e i.val) (V.vertices e (i.val+1))
          (shiftedTrack (V.vertices f) (V.pieces f) t j.val)
          (shiftedTrack (V.vertices f) (V.pieces f) t (j.val+1)) =
          segmentCrossingSign (V.vertices e i.val) (V.vertices e (i.val+1))
            (V.vertices f j.val) (V.vertices f (j.val+1)) := by
  classical
  let Pair := Σ e : Edge, Σ f : {f : Edge // e ≠ f},
    Fin (V.pieces e) × Fin (V.pieces f.val)
  let a : Pair → Plane := fun k => V.vertices k.1 k.2.2.1.val
  let b : Pair → Plane := fun k => V.vertices k.1 (k.2.2.1.val+1)
  let c : Pair → Plane := fun k => V.vertices k.2.1.val k.2.2.2.val
  let d : Pair → Plane := fun k => V.vertices k.2.1.val (k.2.2.2.val+1)
  let qc : Pair → Plane := fun k => trackOffset (V.vertices k.2.1.val) (V.pieces k.2.1.val) k.2.2.2.val
  let qd : Pair → Plane := fun k => trackOffset (V.vertices k.2.1.val) (V.pieces k.2.1.val) (k.2.2.2.val+1)
  have hh (k : Pair) : SegmentPairTransverse (a k) (b k) (c k) (d k) :=
    V.pair_transverse hnorm hstraight htrans k.1 k.2.1.val k.2.1.property k.2.2.1 k.2.2.2
  obtain ⟨δ,hδ,hstable⟩ := exists_shifted_segment_pairs_radius a b c d qc qd hh
  refine ⟨δ,hδ,?_⟩
  intro t ht e f hef i j
  exact hstable t ht ⟨e,⟨f,hef⟩,i,j⟩

end Paper170Geometry.VertexTruncation

end
end

section

/-! One actual oriented circle chart at each vertex, chosen before any cycle or pair of chords. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
variable {D : Paper170.ContinuousDrawing graph}

structure TruncatedSpokeCoordinates (V : VertexTruncation D) where
  frame : Vertex → Plane
  frame_ne_zero : ∀ j, frame j ≠ 0
  frame_length : ∀ j, squaredLength (frame j)=V.radius^2
  node : ∀ j, IncidentEdges graph j → ℝ
  node_injective : ∀ j, Function.Injective (node j)
  point_eq : ∀ j e, similarityPoint (D.vertex j) (frame j) (circlePoint (node j e))=V.spokePort j e

theorem nonempty_truncatedSpokeCoordinates [Fintype Edge] {A : Paper170.AdmissibleDrawing graph}
    (V : VertexTruncation A.toContinuousDrawing) (hnorm : NoAdjacentCrossings A) :
    Nonempty (TruncatedSpokeCoordinates V) := by
  have hex (j : Vertex) := exists_finite_circle_coordinates
    (A.vertex j) V.radius V.radius_pos (V.spokePort j)
    (V.spokePort_injective hnorm j) (V.spokePort_circle j)
  choose u hu hlen node hnode hpoint using hex
  exact ⟨⟨u,hu,hlen,node,hnode,hpoint⟩⟩

namespace TruncatedSpokeCoordinates
variable {V : VertexTruncation D} (C : TruncatedSpokeCoordinates V)

def shiftedPort (j : Vertex) (e : IncidentEdges graph j) (ε : ℝ) : Plane :=
  similarityPoint (D.vertex j) (C.frame j)
    (circleOffset (circlePoint (C.node j e)) (V.spokeScale j e*ε))

def tangentPort (_C : TruncatedSpokeCoordinates V) (j : Vertex) (e : IncidentEdges graph j) (ε : ℝ) : Plane :=
  V.spokePort j e+ε • normalShift (V.spokeDirection j e)

theorem tangentPort_eq (j : Vertex) (e : IncidentEdges graph j) (ε : ℝ) :
    C.tangentPort j e ε = similarityPoint (D.vertex j) (C.frame j)
      (circleTangentOffset (circlePoint (C.node j e)) (V.spokeScale j e*ε)) := by
  have hh := tangentOffset_eq_normalShift (D.vertex j) (C.frame j) (circlePoint (C.node j e))
    (V.spokeDirection j e) (V.spokeDirection_ne_zero j e)
    (by simpa only [C.point_eq] using V.spokePort_ne_center j e)
    (by simpa only [C.point_eq] using V.spokeDirection_parallel j e) ε
  simpa only [C.point_eq,VertexTruncation.spokeScale,tangentPort] using hh.symm

theorem shiftedPort_level (j : Vertex) (e : IncidentEdges graph j) (ε : ℝ) :
    det2 (V.spokeDirection j e) (C.shiftedPort j e ε-V.spokePort j e)=ε := by
  have hh := circleOffset_track_level (D.vertex j) (C.frame j) (circlePoint (C.node j e))
    (V.spokeDirection j e) (V.spokeDirection_ne_zero j e)
    (by simpa only [C.point_eq] using V.spokePort_ne_center j e)
    (by simpa only [C.point_eq] using V.spokeDirection_parallel j e) ε
  simpa only [C.point_eq,VertexTruncation.spokeScale,shiftedPort] using hh

theorem shiftedPort_circle (j : Vertex) (e : IncidentEdges graph j) (ε : ℝ)
    (hε : |V.spokeScale j e*ε| ≤ 1) :
    squaredLength (C.shiftedPort j e ε-D.vertex j)=V.radius^2 := by
  unfold shiftedPort
  rw [similarityPoint_squaredLength,circleOffset_on_circle _ (circlePoint_on_unit_circle _) _ hε,
    mul_one,C.frame_length]

theorem connector_strictly_outside (j : Vertex) (e : IncidentEdges graph j) (ε : ℝ)
    (hε : |V.spokeScale j e*ε| < 1) (hne : ε ≠ 0) (t : ℝ) (ht : 0<t) :
    V.radius^2 < squaredLength (segmentPoint (C.shiftedPort j e ε) (C.tangentPort j e ε) t-D.vertex j) := by
  rw [C.tangentPort_eq]
  have hh := physical_circleConnector_strictly_outside (D.vertex j) (C.frame j)
    (circlePoint (C.node j e)) (C.frame_ne_zero j) (circlePoint_on_unit_circle _)
    (V.spokeScale j e*ε) hε (mul_ne_zero (V.spokeScale_ne_zero j e) hne) t ht
  simpa only [C.frame_length,shiftedPort] using hh

theorem exists_vertex_average_radius [Fintype Edge] (j : Vertex) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ∀ a b c d : IncidentEdges graph j,
      a ≠ b → c ≠ d →
      (segmentCrossingSign (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j c t) (C.shiftedPort j d t)+
        segmentCrossingSign (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j c (-t)) (C.shiftedPort j d (-t)))/2 =
      chordEndpointPairing (C.node j a) (C.node j b) (C.node j c) (C.node j d) := by
  classical
  obtain ⟨δ,hδ,hh⟩ := physical_spoke_average_in_similarity (D.vertex j) (C.frame j) (C.frame_ne_zero j)
    (C.node j) (V.spokeScale j) (C.node_injective j) (V.spokeScale_ne_zero j)
  refine ⟨δ,hδ,?_⟩
  intro t ht hsmall a b c d hab hcd
  simpa only [C.point_eq,shiftedPort] using hh t ht hsmall a b c d hab hcd

end TruncatedSpokeCoordinates
end Paper170Geometry

end
end

section

/-! One physical two-sided perturbation works for every ordered pair of actual edge tracks, including shared edges. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.VertexTruncation
open scoped BigOperators
variable {D : Paper170.AdmissibleDrawing graph}

theorem exists_all_edge_shift_radius [Fintype Vertex] [Fintype Edge] (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ≠ 0 → |t| < δ → ∀ e f : Edge,
      ∀ i : Fin (V.pieces e), ∀ j : Fin (V.pieces f),
        SegmentPairTransverse (V.vertices e i.val) (V.vertices e (i.val+1))
          (shiftedTrack (V.vertices f) (V.pieces f) t j.val)
          (shiftedTrack (V.vertices f) (V.pieces f) t (j.val+1)) ∧
        segmentCrossingSign (V.vertices e i.val) (V.vertices e (i.val+1))
          (shiftedTrack (V.vertices f) (V.pieces f) t j.val)
          (shiftedTrack (V.vertices f) (V.pieces f) t (j.val+1)) =
          if e=f then 0 else segmentCrossingSign (V.vertices e i.val) (V.vertices e (i.val+1))
            (V.vertices f j.val) (V.vertices f (j.val+1)) := by
  classical
  obtain ⟨δ₀,hδ₀,hother⟩ := V.exists_distinct_edge_shift_radius hnorm hstraight htrans
  choose radius hpos hself using V.offset_avoidance
  obtain ⟨δ₁,hδ₁,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun e _ => hpos e)
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,?_⟩
  intro t ht hsmall e f i j
  by_cases hef : e=f
  · subst f
    have hno := hself e t ht ((hsmall.trans_le (min_le_right _ _)).trans (hbound e (Finset.mem_univ _))) i j
    refine ⟨?_,?_⟩
    · intro s hs u hu he
      exact False.elim (hno ⟨s,hs,u,hu,he⟩)
    · have hp : ¬ SegmentsCrossProperly (V.vertices e i.val) (V.vertices e (i.val+1))
          (shiftedTrack (V.vertices e) (V.pieces e) t j.val)
          (shiftedTrack (V.vertices e) (V.pieces e) t (j.val+1)) :=
        fun h => hno (closedSegmentsMeet_of_proper _ _ _ _ h)
      simp [segmentCrossingSign,hp]
  · obtain ⟨hT,hS⟩ := hother t (hsmall.trans_le (min_le_left _ _)) e f hef i j
    exact ⟨hT,by simpa only [ite_eq_right hef] using hS⟩

theorem exists_uniform_track_intersections [Fintype Vertex] [Fintype Edge] (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ≠ 0 → |t| < δ → ∀ e f : Edge,
      polygonIntersection (V.vertices e) (shiftedTrack (V.vertices f) (V.pieces f) t) (V.pieces e) (V.pieces f) =
        if e=f then 0 else polygonIntersection (V.vertices e) (V.vertices f) (V.pieces e) (V.pieces f) := by
  classical
  obtain ⟨δ,hδ,hh⟩ := V.exists_all_edge_shift_radius hnorm hstraight htrans
  refine ⟨δ,hδ,?_⟩
  intro t ht hsmall e f
  by_cases hef : e=f
  · rw [ite_eq_left hef]
    unfold polygonIntersection
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    simpa only [ite_eq_left hef] using
      (hh t ht hsmall e f ⟨i,Finset.mem_range.mp hi⟩ ⟨j,Finset.mem_range.mp hj⟩).2
  · rw [ite_eq_right hef]
    unfold polygonIntersection
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [ite_eq_right hef] using
      (hh t ht hsmall e f ⟨i,Finset.mem_range.mp hi⟩ ⟨j,Finset.mem_range.mp hj⟩).2

end Paper170Geometry.VertexTruncation

end
end

section

/-! The ends of each actual shifted track are precisely the ends of its two circle connectors. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.VertexTruncation
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

def leftIncident (_V : VertexTruncation D) (e : Edge) : IncidentEdges graph ((graph.src e)) := ⟨e,Or.inl rfl⟩
def rightIncident (_V : VertexTruncation D) (e : Edge) : IncidentEdges graph ((graph.dst e)) := ⟨e,Or.inr rfl⟩

theorem vertices_first (e : Edge) : V.vertices e 0=V.startPort e :=
  (V.chain e).truncatedVertices_first V.radius

theorem vertices_last (e : Edge) : V.vertices e (V.pieces e)=V.endPort e :=
  (V.chain e).truncatedVertices_last (V.pieces_pos e) V.radius

theorem spokePort_left (e : Edge) :
    V.spokePort ((graph.src e)) (V.leftIncident e)=V.startPort e := by
  simp [spokePort,drawingSpokePort,leftIncident,startPort]

theorem spokePort_right (e : Edge) :
    V.spokePort ((graph.dst e)) (V.rightIncident e)=V.endPort e := by
  simp [spokePort,drawingSpokePort,rightIncident,endPort,(graph.loopless e).symm]

theorem shiftedTrack_first (C : TruncatedSpokeCoordinates V) (e : Edge) (ε : ℝ) :
    shiftedTrack (V.vertices e) (V.pieces e) ε 0=
      C.tangentPort ((graph.src e)) (V.leftIncident e) ε := by
  simp [shiftedTrack,trackOffset,TruncatedSpokeCoordinates.tangentPort,spokeDirection,
    spokeIndex,leftIncident,V.vertices_first,spokePort,drawingSpokePort,startPort]

theorem shiftedTrack_last (C : TruncatedSpokeCoordinates V) (e : Edge) (ε : ℝ) :
    shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e)=
      C.tangentPort ((graph.dst e)) (V.rightIncident e) ε := by
  have hn : V.pieces e ≠ 0 := ne_of_gt (V.pieces_pos e)
  simp [shiftedTrack,trackOffset,hn,TruncatedSpokeCoordinates.tangentPort,spokeDirection,
    spokeIndex,rightIncident,V.vertices_last,spokePort,drawingSpokePort,endPort,(graph.loopless e).symm]

end Paper170Geometry.VertexTruncation

end
end

section

/-! Every original/shifted vertex endpoint is distinct for either sufficiently small nonzero displacement. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
variable {D : Paper170.ContinuousDrawing graph} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem continuous_shiftedPort (j : Vertex) (e : IncidentEdges graph j) :
    Continuous (C.shiftedPort j e) := by
  change Continuous (fun ε : ℝ => similarityPoint (D.vertex j) (C.frame j)
    (circleOffset (circlePoint (C.node j e)) (V.spokeScale j e*ε)))
  dsimp [similarityPoint,circleOffset,rotateQuarter]
  fun_prop

theorem shiftedPort_zero (j : Vertex) (e : IncidentEdges graph j) :
    C.shiftedPort j e 0=V.spokePort j e := by
  simp only [shiftedPort,mul_zero,circleOffset_zero,C.point_eq]

theorem shiftedPort_ne_original (j : Vertex) (e : IncidentEdges graph j)
    (ε : ℝ) (hε : ε ≠ 0) : C.shiftedPort j e ε ≠ V.spokePort j e := by
  intro he
  have hh := C.shiftedPort_level j e ε
  rw [he,sub_self] at hh
  have hz : det2 (V.spokeDirection j e) (0 : Plane)=0 := by simp [det2]
  rw [hz] at hh
  exact hε hh.symm

theorem exists_endpoint_separation_radius [Fintype Edge] (j : Vertex) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ →
      (∀ e f : IncidentEdges graph j, V.spokePort j e ≠ C.shiftedPort j f ε) ∧
      Function.Injective (fun e : IncidentEdges graph j => C.shiftedPort j e ε) := by
  have hinj : Function.Injective (fun e : IncidentEdges graph j => C.shiftedPort j e 0) := by
    intro e f he
    have hh : circlePoint (C.node j e)=circlePoint (C.node j f) := by
      apply similarityPoint_injective (D.vertex j) (C.frame j) (C.frame_ne_zero j)
      simpa only [shiftedPort,mul_zero,circleOffset_zero] using he
    exact C.node_injective j (circlePoint_injective hh)
  obtain ⟨δ,hδ,hh⟩ := finite_moving_points_separation (C.shiftedPort j)
    (C.continuous_shiftedPort j) hinj
  refine ⟨δ,hδ,?_⟩
  intro ε hε hsmall
  constructor
  · intro e f
    by_cases hef : e=f
    · subst f
      exact (C.shiftedPort_ne_original j e ε hε).symm
    · simpa only [C.shiftedPort_zero] using (hh ε hsmall e f hef).1
  · intro e f he
    by_contra hef
    exact (hh ε hsmall e f hef).2 he

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! Signed intersections are actual segment-traversal sums; their support is controlled by spatial crossing points. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.VertexTruncation
open scoped BigOperators
variable {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)

theorem piece_subset_range (e : Edge) (i : ℕ) (hi : i<V.pieces e) :
    segment ℝ (V.vertices e i) (V.vertices e (i+1)) ⊆ Set.range (V.path e) := by
  exact ((V.chain e).truncated (V.pieces_pos e) V.radius V.radius_pos
    (V.weak_short e).1 (V.weak_short e).2).piece_subset_path_range i hi

def signedIntersection (e f : Edge) : ℝ :=
  if e=f then 0 else polygonIntersection (V.vertices e) (V.vertices f) (V.pieces e) (V.pieces f)

theorem signedIntersection_self (e : Edge) : V.signedIntersection e e=0 := by
  simp [signedIntersection]

theorem signedIntersection_swap (e f : Edge) : V.signedIntersection f e = -V.signedIntersection e f := by
  by_cases h : e=f
  · subst f
    simp [V.signedIntersection_self]
  · simp only [signedIntersection,ite_eq_right h,ite_eq_right (Ne.symm h)]
    exact polygonIntersection_swap _ _ _ _

theorem signedIntersection_zero_of_pairCrossings_empty {A : Paper170.AdmissibleDrawing graph}
    (V : VertexTruncation A.toContinuousDrawing) (e f : Edge)
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
      have hxe : x ∈ Paper170.edgeInterior A.toContinuousDrawing e := by
        apply V.range_subset_edgeInterior e
        apply V.piece_subset_range e i (Finset.mem_range.mp hi)
        rw [← Path.range_segment]
        exact ⟨⟨s,⟨hs.1.le,hs.2.le⟩⟩,by simp only [Path.segment_apply,AffineMap.lineMap_apply_module,x,segmentPoint]⟩
      have hxf : x ∈ Paper170.edgeInterior A.toContinuousDrawing f := by
        apply V.range_subset_edgeInterior f
        apply V.piece_subset_range f j (Finset.mem_range.mp hj)
        rw [← Path.range_segment]
        refine ⟨⟨t,⟨ht.1.le,ht.2.le⟩⟩,?_⟩
        simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,x,segmentPoint] using he.symm
      have hx : x ∈ pairCrossings A e f := by
        apply Finset.mem_filter.mpr
        exact ⟨by simpa using (show x ∈ Paper170.crossingPoints A.toContinuousDrawing from ⟨e,f,hef,hxe,hxf⟩),hef,hxe,hxf⟩
      rw [hempty] at hx
      exact Finset.notMem_empty x hx
    simp [segmentCrossingSign,hnot]

theorem pairCrossings_pos_of_signedIntersection_ne_zero {A : Paper170.AdmissibleDrawing graph}
    (V : VertexTruncation A.toContinuousDrawing) (e f : Edge)
    (h : V.signedIntersection e f ≠ 0) : 0 < (pairCrossings A e f).card := by
  by_contra hh
  have hz : (pairCrossings A e f).card=0 := by omega
  exact h (V.signedIntersection_zero_of_pairCrossings_empty e f (Finset.card_eq_zero.mp hz))

theorem signedIntersection_adjacent_zero {A : Paper170.AdmissibleDrawing graph}
    (V : VertexTruncation A.toContinuousDrawing) (hnorm : NoAdjacentCrossings A)
    (e f : Edge) (hadj : graph.src e = graph.src f ∨ graph.src e = graph.dst f ∨
      graph.dst e = graph.src f ∨ graph.dst e = graph.dst f) : V.signedIntersection e f=0 := by
  apply V.signedIntersection_zero_of_pairCrossings_empty e f
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨_, hef, he, hf⟩ := Finset.mem_filter.mp hx
  have hm : x ∈ Paper170.edgeInterior A.toContinuousDrawing e ∩
      Paper170.edgeInterior A.toContinuousDrawing f := ⟨he, hf⟩
  rw [hnorm.eq_empty e f hef hadj] at hm
  exact hm.elim

end Paper170Geometry.VertexTruncation

end
end

section

/-! An actual boundary port belongs to exactly its incident truncated endpoint piece. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.VertexTruncation

theorem spokePort_interior {D : Paper170.ContinuousDrawing graph} (V : VertexTruncation D)
    (j : Vertex) (f : IncidentEdges graph j) : V.spokePort j f ∈ Paper170.edgeInterior D f.val :=
  drawingSpokePort_interior D V.chain V.minimal V.radius V.radius_pos V.weak_short j f

theorem spokePort_piece_unique {D : Paper170.AdmissibleDrawing graph} (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (j : Vertex) (f : IncidentEdges graph j)
    (e : Edge) (i : Fin (V.pieces e))
    (hx : V.spokePort j f ∈ segment ℝ (V.vertices e i.val) (V.vertices e (i.val+1))) :
    e=f.val ∧ i.val=V.spokeIndex j f := by
  have hcircle : V.spokePort j f ∈ closedRoundDisk (D.vertex j) V.radius := by
    change squaredLength (V.spokePort j f-D.vertex j) ≤ V.radius^2
    rw [V.spokePort_circle]
  have he : e=f.val := by
    by_contra hef
    have hcross : V.spokePort j f ∈ Paper170.crossingPoints D.toContinuousDrawing :=
      ⟨e,f.val,hef,V.range_subset_edgeInterior e (V.piece_subset_range e i.val i.isLt hx),V.spokePort_interior j f⟩
    exact Set.disjoint_left.mp (V.crossing_free_disks hnorm j) hcircle hcross
  have hcase : (j=(graph.src e) ∧ i.val=0) ∨ (j=(graph.dst e) ∧ i.val+1=V.pieces e) := by
    by_contra hh
    have hold := (V.chain e).truncated_piece_subset V.radius V.radius_pos
      (V.weak_short e).1 (V.weak_short e).2 i.val i.isLt hx
    exact Set.disjoint_left.mp (V.piece_clearance j e i hh) hcircle hold
  refine ⟨he,?_⟩
  unfold spokeIndex
  split_ifs with hj
  · rcases hcase with hh | hh
    · exact hh.2
    · have hbad : graph.src f.val = graph.dst e := hj.symm.trans hh.1
      exact False.elim ((graph.loopless e) ((congrArg graph.src he).trans hbad))
  · rcases hcase with hh | hh
    · exact False.elim (hj (hh.1.trans (congrArg (fun g : Edge => (graph.src g)) he)))
    · have hn : V.pieces e=V.pieces f.val := congrArg V.pieces he
      omega

end Paper170Geometry.VertexTruncation

end
end

end OAI
