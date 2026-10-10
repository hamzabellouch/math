import OAI.Combinatorics.CompleteCrossing.DartPaths
import OAI.Combinatorics.CompleteCrossing.VertexChords
import OAI.Combinatorics.Crossing.CyclicSumArithmetic
import OAI.Combinatorics.Crossing.StraightChainIntersections
import OAI.Combinatorics.Crossing.StraightChainTransversality

namespace OAI

/-! Signed dart and cycle intersections, passage pairing, and endpoint averaging. -/

section

/-! Complete shifted edge paths have exactly the original signed edge intersections; the two actual connectors contribute zero. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_complete_edge_intersection_radius [Fintype Vertex] [Fintype Edge] (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ → ∀ e f : Edge,
      (V.trackChain e).Transverse (C.shiftedEdgeChain f ε) ∧
      polygonIntersection (V.trackChain e).vertices (C.shiftedEdgeChain f ε).vertices
        (V.trackChain e).pieces (C.shiftedEdgeChain f ε).pieces=V.signedIntersection e f := by
  obtain ⟨δ₀,hδ₀,hT⟩ := V.exists_all_edge_shift_radius hnorm hstraight htrans
  obtain ⟨δ₁,hδ₁,hI⟩ := V.exists_uniform_track_intersections hnorm hstraight htrans
  obtain ⟨δ₂,hδ₂,hC⟩ := C.exists_all_connector_track_radius hnorm
  let δ := min δ₀ (min δ₁ δ₂)
  have hδ : 0<δ := lt_min hδ₀ (lt_min hδ₁ hδ₂)
  have hb₀ : δ≤δ₀ := min_le_left _ _
  have hb₁ : δ≤δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hb₂ : δ≤δ₂ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ,hδ,?_⟩
  intro ε hε hsmall e f
  have hconn (j : Vertex) (g : IncidentEdges graph j) :
      (V.trackChain e).Transverse (C.connectorChain j g ε) := by
    apply PolygonalChain.transverse_single_right
    intro i
    exact segmentPairTransverse_of_not_meet _ _ _ _ (hC ε hε (hsmall.trans_le hb₂) j g e i)
  have hmid : (V.trackChain e).Transverse (C.shiftedTrackChain f ε) := by
    intro i j
    exact (hT ε hε (hsmall.trans_le hb₀) e f i j).1
  have hzero (j : Vertex) (g : IncidentEdges graph j) :
      polygonIntersection (V.trackChain e).vertices (C.connectorChain j g ε).vertices (V.trackChain e).pieces 1=0 := by
    apply PolygonalChain.intersection_single_right_zero
    intro i
    exact hC ε hε (hsmall.trans_le hb₂) j g e i
  constructor
  · change (V.trackChain e).Transverse
      (((C.connectorChain ((graph.src f)) (V.leftIncident f) ε).join (C.shiftedTrackChain f ε)).join
        (C.connectorChain ((graph.dst f)) (V.rightIncident f) ε).reverse)
    apply PolygonalChain.transverse_join_right
    · exact PolygonalChain.transverse_join_right _ _ _ (hconn _ _) hmid
    · exact (V.trackChain e).transverse_reverse_right _ (hconn _ _)
  · rw [C.shiftedEdgeChain_intersection_right,hzero,hzero,zero_add,sub_zero]
    exact hI ε hε (hsmall.trans_le hb₁) e f

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! Complete edge paths and vertex chords have zero cross-type intersection sums, with all seams verified. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_chord_edge_radius [Fintype Vertex] [Fintype Edge] (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ →
      (∀ j (a b : IncidentEdges graph j) e,
        (V.chordChain j a b).Transverse (C.shiftedEdgeChain e ε) ∧
        polygonIntersection (V.chordChain j a b).vertices (C.shiftedEdgeChain e ε).vertices
          (V.chordChain j a b).pieces (C.shiftedEdgeChain e ε).pieces=0) ∧
      (∀ j (a b : IncidentEdges graph j) e,
        (V.trackChain e).Transverse (C.shiftedChordChain j a b ε) ∧
        polygonIntersection (V.trackChain e).vertices (C.shiftedChordChain j a b ε).vertices
          (V.trackChain e).pieces (C.shiftedChordChain j a b ε).pieces=0) := by
  obtain ⟨δ,hδ,hh⟩ := C.exists_cross_type_radius hnorm
  refine ⟨δ,hδ,?_⟩
  intro ε hε hsmall
  obtain ⟨hTC,hTChord,hChordT,hChordC,hChordChord,hOther⟩ := hh ε hε hsmall
  constructor
  · intro j a b e
    have hconn (k : Vertex) (f : IncidentEdges graph k) :
        (V.chordChain j a b).Transverse (C.connectorChain k f ε) := by
      apply PolygonalChain.transverse_single_single
      exact segmentPairTransverse_of_not_meet _ _ _ _ (hChordC j k a b f)
    have hmid : (V.chordChain j a b).Transverse (C.shiftedTrackChain e ε) := by
      apply PolygonalChain.transverse_single_left
      intro i
      exact segmentPairTransverse_of_not_meet _ _ _ _ (hChordT j a b e i)
    have hzconn (k : Vertex) (f : IncidentEdges graph k) :
        polygonIntersection (V.chordChain j a b).vertices (C.connectorChain k f ε).vertices 1 1=0 := by
      rw [VertexTruncation.chordChain,connectorChain,PolygonalChain.intersection_single_single]
      exact segmentCrossingSign_eq_zero_of_not_meet _ _ _ _ (hChordC j k a b f)
    have hzmid : polygonIntersection (V.chordChain j a b).vertices
        (shiftedTrack (V.vertices e) (V.pieces e) ε) 1 (V.pieces e)=0 := by
      apply (C.shiftedTrackChain e ε).intersection_single_left_zero
      intro i
      exact hChordT j a b e i
    constructor
    · change (V.chordChain j a b).Transverse
        (((C.connectorChain ((graph.src e)) (V.leftIncident e) ε).join (C.shiftedTrackChain e ε)).join
          (C.connectorChain ((graph.dst e)) (V.rightIncident e) ε).reverse)
      apply PolygonalChain.transverse_join_right
      · exact PolygonalChain.transverse_join_right _ _ _ (hconn _ _) hmid
      · exact (V.chordChain j a b).transverse_reverse_right _ (hconn _ _)
    · change polygonIntersection (V.chordChain j a b).vertices (C.shiftedEdgeChain e ε).vertices 1 _=0
      rw [C.shiftedEdgeChain_intersection_right,hzconn,hzconn,hzmid]
      norm_num
  · intro j a b e
    constructor
    · apply PolygonalChain.transverse_single_right
      intro i
      exact segmentPairTransverse_of_not_meet _ _ _ _ (hTChord j a b e i)
    · apply PolygonalChain.intersection_single_right_zero
      intro i
      exact hTChord j a b e i

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! Actual vertex-chord chains have precisely the local two-sided averaged endpoint pairing. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem chordChain_intersection (j k : Vertex) (a b : IncidentEdges graph j)
    (c d : IncidentEdges graph k) (ε : ℝ) :
    polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain k c d ε).vertices 1 1=
      segmentCrossingSign (V.spokePort j a) (V.spokePort j b) (C.shiftedPort k c ε) (C.shiftedPort k d ε) := by
  rw [VertexTruncation.chordChain,shiftedChordChain,PolygonalChain.intersection_single_single]

theorem exists_vertex_chord_chain_radius [Fintype Vertex] [Fintype Edge] (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0<δ ∧
      (∀ ε : ℝ, ε ≠ 0 → |ε|<δ → ∀ j k (a b : IncidentEdges graph j) (c d : IncidentEdges graph k),
        a ≠ b → c ≠ d → (V.chordChain j a b).Transverse (C.shiftedChordChain k c d ε)) ∧
      (∀ ε : ℝ, ε ≠ 0 → |ε|<δ → ∀ j k, j ≠ k → ∀ (a b : IncidentEdges graph j) (c d : IncidentEdges graph k),
        polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain k c d ε).vertices 1 1=0) ∧
      (∀ t : ℝ, 0<t → t<δ → ∀ j (a b c d : IncidentEdges graph j), a ≠ b → c ≠ d →
        (polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain j c d t).vertices 1 1+
          polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain j c d (-t)).vertices 1 1)/2=
            chordEndpointPairing (C.node j a) (C.node j b) (C.node j c) (C.node j d)) := by
  obtain ⟨δ₀,hδ₀,hgeo⟩ := C.exists_cross_type_radius hnorm
  obtain ⟨δ₁,hδ₁,havg⟩ := C.exists_uniform_average_radius
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,?_,?_,?_⟩
  · intro ε hε hsmall j k a b c d hab hcd
    have hh := (hgeo ε hε (hsmall.trans_le (min_le_left _ _))).2.2.2.2.1 j k a b c d hab hcd
    exact PolygonalChain.transverse_single_single _ _ _ _ hh
  · intro ε hε hsmall j k hjk a b c d
    rw [C.chordChain_intersection]
    exact segmentCrossingSign_eq_zero_of_not_meet _ _ _ _
      ((hgeo ε hε (hsmall.trans_le (min_le_left _ _))).2.2.2.2.2 j k hjk a b c d)
  · intro t ht hsmall j a b c d hab hcd
    rw [C.chordChain_intersection,C.chordChain_intersection]
    exact havg t ht (hsmall.trans_le (min_le_right _ _)) j a b c d hab hcd

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! Actual oriented dart intersections, including opposite traversals of shared edges. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem dart_pair_intersection {ε : ℝ} (a b : OrientedDart graph)
    (h : ∀ e f, (V.trackChain e).Transverse (C.shiftedEdgeChain f ε) ∧
      polygonIntersection (V.trackChain e).vertices (C.shiftedEdgeChain f ε).vertices
        (V.trackChain e).pieces (C.shiftedEdgeChain f ε).pieces=V.signedIntersection e f) :
    (V.dartTrackChain a).Transverse (C.shiftedDartChain b ε) ∧
      polygonIntersection (V.dartTrackChain a).vertices (C.shiftedDartChain b ε).vertices
        (V.dartTrackChain a).pieces (C.shiftedDartChain b ε).pieces=
          dartSign a*dartSign b*V.signedIntersection (OrientedDart.edge a) (OrientedDart.edge b) := by
  rcases orientedDart_cases a with ⟨e,rfl⟩ | ⟨e,rfl⟩ <;>
    rcases orientedDart_cases b with ⟨f,rfl⟩ | ⟨f,rfl⟩
  · obtain ⟨hT,hI⟩ := h e f
    refine ⟨hT,?_⟩
    change polygonIntersection (V.trackChain e).vertices (C.shiftedEdgeChain f ε).vertices
      (V.trackChain e).pieces (C.shiftedEdgeChain f ε).pieces=1*1*V.signedIntersection e f
    simpa only [one_mul] using hI
  · obtain ⟨hT,hI⟩ := h e f
    refine ⟨(V.trackChain e).transverse_reverse_right _ hT,?_⟩
    change polygonIntersection (V.trackChain e).vertices (C.shiftedEdgeChain f ε).reverse.vertices
      (V.trackChain e).pieces (C.shiftedEdgeChain f ε).reverse.pieces=1*(-1)*V.signedIntersection e f
    rw [PolygonalChain.intersection_reverse_right,hI]
    ring
  · obtain ⟨hT,hI⟩ := h e f
    refine ⟨(V.trackChain e).transverse_reverse_left _ hT,?_⟩
    change polygonIntersection (V.trackChain e).reverse.vertices (C.shiftedEdgeChain f ε).vertices
      (V.trackChain e).reverse.pieces (C.shiftedEdgeChain f ε).pieces=(-1)*1*V.signedIntersection e f
    rw [PolygonalChain.intersection_reverse_left,hI]
    ring
  · obtain ⟨hT,hI⟩ := h e f
    refine ⟨(V.trackChain e).reverse.transverse_reverse_right _
      ((V.trackChain e).transverse_reverse_left _ hT),?_⟩
    change polygonIntersection (V.trackChain e).reverse.vertices (C.shiftedEdgeChain f ε).reverse.vertices
      (V.trackChain e).reverse.pieces (C.shiftedEdgeChain f ε).reverse.pieces=(-1)*(-1)*V.signedIntersection e f
    rw [PolygonalChain.intersection_reverse_left,PolygonalChain.intersection_reverse_right,hI]
    ring

theorem chord_dart_intersection {ε : ℝ} (j : Vertex) (a b : IncidentEdges graph j)
    (d : OrientedDart graph)
    (h : ∀ e, (V.chordChain j a b).Transverse (C.shiftedEdgeChain e ε) ∧
      polygonIntersection (V.chordChain j a b).vertices (C.shiftedEdgeChain e ε).vertices
        (V.chordChain j a b).pieces (C.shiftedEdgeChain e ε).pieces=0) :
    (V.chordChain j a b).Transverse (C.shiftedDartChain d ε) ∧
      polygonIntersection (V.chordChain j a b).vertices (C.shiftedDartChain d ε).vertices
        (V.chordChain j a b).pieces (C.shiftedDartChain d ε).pieces=0 := by
  rcases orientedDart_cases d with ⟨e,rfl⟩ | ⟨e,rfl⟩
  · exact h e
  · obtain ⟨hT,hI⟩ := h e
    refine ⟨(V.chordChain j a b).transverse_reverse_right _ hT,?_⟩
    change polygonIntersection (V.chordChain j a b).vertices (C.shiftedEdgeChain e ε).reverse.vertices
      (V.chordChain j a b).pieces (C.shiftedEdgeChain e ε).reverse.pieces=0
    rw [PolygonalChain.intersection_reverse_right,hI,neg_zero]

theorem dart_chord_intersection {ε : ℝ} (j : Vertex) (a b : IncidentEdges graph j)
    (d : OrientedDart graph)
    (h : ∀ e, (V.trackChain e).Transverse (C.shiftedChordChain j a b ε) ∧
      polygonIntersection (V.trackChain e).vertices (C.shiftedChordChain j a b ε).vertices
        (V.trackChain e).pieces (C.shiftedChordChain j a b ε).pieces=0) :
    (V.dartTrackChain d).Transverse (C.shiftedChordChain j a b ε) ∧
      polygonIntersection (V.dartTrackChain d).vertices (C.shiftedChordChain j a b ε).vertices
        (V.dartTrackChain d).pieces (C.shiftedChordChain j a b ε).pieces=0 := by
  rcases orientedDart_cases d with ⟨e,rfl⟩ | ⟨e,rfl⟩
  · exact h e
  · obtain ⟨hT,hI⟩ := h e
    refine ⟨(V.trackChain e).transverse_reverse_left _ hT,?_⟩
    change polygonIntersection (V.trackChain e).reverse.vertices (C.shiftedChordChain j a b ε).vertices
      (V.trackChain e).reverse.pieces (C.shiftedChordChain j a b ε).pieces=0
    rw [PolygonalChain.intersection_reverse_left,hI,neg_zero]

theorem exists_dart_intersection_radius [Fintype Vertex] [Fintype Edge] (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε| < δ →
      (∀ a b : OrientedDart graph,
        (V.dartTrackChain a).Transverse (C.shiftedDartChain b ε) ∧
        polygonIntersection (V.dartTrackChain a).vertices (C.shiftedDartChain b ε).vertices
          (V.dartTrackChain a).pieces (C.shiftedDartChain b ε).pieces=
            dartSign a*dartSign b*V.signedIntersection (OrientedDart.edge a) (OrientedDart.edge b)) ∧
      (∀ j (a b : IncidentEdges graph j) d,
        (V.chordChain j a b).Transverse (C.shiftedDartChain d ε) ∧
        polygonIntersection (V.chordChain j a b).vertices (C.shiftedDartChain d ε).vertices
          (V.chordChain j a b).pieces (C.shiftedDartChain d ε).pieces=0) ∧
      (∀ j (a b : IncidentEdges graph j) d,
        (V.dartTrackChain d).Transverse (C.shiftedChordChain j a b ε) ∧
        polygonIntersection (V.dartTrackChain d).vertices (C.shiftedChordChain j a b ε).vertices
          (V.dartTrackChain d).pieces (C.shiftedChordChain j a b ε).pieces=0) := by
  obtain ⟨δ₀,hδ₀,h₀⟩ := C.exists_complete_edge_intersection_radius hnorm hstraight htrans
  obtain ⟨δ₁,hδ₁,h₁⟩ := C.exists_chord_edge_radius hnorm
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,?_⟩
  intro ε hε hs
  have he := h₀ ε hε (hs.trans_le (min_le_left _ _))
  obtain ⟨hcd,hdc⟩ := h₁ ε hε (hs.trans_le (min_le_right _ _))
  exact ⟨fun a b => C.dart_pair_intersection a b he,
    fun j a b d => C.chord_dart_intersection j a b d (hcd j a b),
    fun j a b d => C.dart_chord_intersection j a b d (hdc j a b)⟩

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! Every actual cycle-block intersection splits into its edge term and its vertex-chord term. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry

namespace PolygonalChain
variable {O T : Set Plane} {a b c d e f : Plane}

theorem intersection_join_join (P : PolygonalChain O a b) (Q : PolygonalChain O b c)
    (R : PolygonalChain T d e) (S : PolygonalChain T e f) :
    polygonIntersection (P.join Q).vertices (R.join S).vertices (P.join Q).pieces (R.join S).pieces=
      polygonIntersection P.vertices R.vertices P.pieces R.pieces+
      polygonIntersection P.vertices S.vertices P.pieces S.pieces+
      polygonIntersection Q.vertices R.vertices Q.pieces R.pieces+
      polygonIntersection Q.vertices S.vertices Q.pieces S.pieces := by
  rw [Zarankiewicz.PolygonalChain.intersection_join_left,
    Zarankiewicz.PolygonalChain.intersection_join_right,
    Zarankiewicz.PolygonalChain.intersection_join_right]
  ring

theorem transverse_join_join (P : PolygonalChain O a b) (Q : PolygonalChain O b c)
    (R : PolygonalChain T d e) (S : PolygonalChain T e f)
    (hPR : P.Transverse R) (hPS : P.Transverse S) (hQR : Q.Transverse R) (hQS : Q.Transverse S) :
    (P.join Q).Transverse (R.join S) :=
  P.transverse_join_left Q (R.join S)
    (R.transverse_join_right S P hPR hPS) (R.transverse_join_right S Q hQR hQS)

end PolygonalChain
namespace TruncatedSpokeCoordinates
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

def passageIntersection (d f : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
    (i j : ℕ) (ε : ℝ) : ℝ :=
  polygonIntersection (V.chordChain (d i).snd (dartTargetIncident (d i)) (dartPassageNext d hd i)).vertices
    (C.shiftedChordChain (f j).snd (dartTargetIncident (f j)) (dartPassageNext f hf j) ε).vertices 1 1

theorem exists_cycle_block_radius [Fintype Vertex] [Fintype Edge] (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε| < δ →
      ∀ (d f : ℕ → OrientedDart graph)
        (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst) (i j : ℕ),
      OrientedDart.edge (d (i+1)) ≠ OrientedDart.edge (d i) →
      OrientedDart.edge (f (j+1)) ≠ OrientedDart.edge (f j) →
      (V.dartCycleBlock d hd i).Transverse (C.shiftedCycleBlock f hf ε j) ∧
      polygonIntersection (V.dartCycleBlock d hd i).vertices (C.shiftedCycleBlock f hf ε j).vertices
        (V.dartCycleBlock d hd i).pieces (C.shiftedCycleBlock f hf ε j).pieces=
          dartSign (d i)*dartSign (f j)*
            V.signedIntersection (OrientedDart.edge (d i)) (OrientedDart.edge (f j))+
              C.passageIntersection d f hd hf i j ε := by
  obtain ⟨δ₀,hδ₀,h₀⟩ := C.exists_dart_intersection_radius hnorm hstraight htrans
  obtain ⟨δ₁,hδ₁,h₁,-,-⟩ := C.exists_vertex_chord_chain_radius hnorm
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,?_⟩
  intro ε hε hs d f hd hf i j hdi hfj
  obtain ⟨hdd,hcd,hdc⟩ := h₀ ε hε (hs.trans_le (min_le_left _ _))
  have hcc := h₁ ε hε (hs.trans_le (min_le_right _ _))
    (d i).snd (f j).snd (dartTargetIncident (d i)) (dartPassageNext d hd i)
      (dartTargetIncident (f j)) (dartPassageNext f hf j)
        (dartPassage_ne d hd i hdi) (dartPassage_ne f hf j hfj)
  obtain ⟨hDD,hDI⟩ := hdd (d i) (f j)
  obtain ⟨hCD,hCI⟩ := hcd (d i).snd (dartTargetIncident (d i)) (dartPassageNext d hd i) (f j)
  obtain ⟨hDC,hIC⟩ := hdc (f j).snd (dartTargetIncident (f j)) (dartPassageNext f hf j) (d i)
  constructor
  · exact PolygonalChain.transverse_join_join _ _ _ _ hDD hDC hCD hcc
  · change polygonIntersection
      ((V.dartTrackChain (d i)).join (V.chordChain (d i).snd (dartTargetIncident (d i)) (dartPassageNext d hd i))).vertices
      ((C.shiftedDartChain (f j) ε).join (C.shiftedChordChain (f j).snd (dartTargetIncident (f j)) (dartPassageNext f hf j) ε)).vertices
      ((V.dartTrackChain (d i)).join (V.chordChain (d i).snd (dartTargetIncident (d i)) (dartPassageNext d hd i))).pieces
      ((C.shiftedDartChain (f j) ε).join (C.shiftedChordChain (f j).snd (dartTargetIncident (f j)) (dartPassageNext f hf j) ε)).pieces=_
    rw [PolygonalChain.intersection_join_join,hDI,hIC,hCI,add_zero,add_zero]
    rfl

end TruncatedSpokeCoordinates
end Paper170Geometry

end
end

section

/-! The global sum is derived from the actual closed polygonal curves and every one of their traversals. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
open scoped BigOperators
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_closed_cycle_intersection_radius [Fintype Vertex] [Fintype Edge] (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε| < δ →
      ∀ (d f : ℕ → OrientedDart graph)
        (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
        (N K : ℕ), d N=d 0 → f K=f 0 →
        (∀ i, i < N → OrientedDart.edge (d (i+1)) ≠ OrientedDart.edge (d i)) →
        (∀ j, j < K → OrientedDart.edge (f (j+1)) ≠ OrientedDart.edge (f j)) →
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
        (dartSign (d i)*dartSign (f j)*
          V.signedIntersection (OrientedDart.edge (d i)) (OrientedDart.edge (f j))+
            C.passageIntersection d f hd hf i j ε)=0 := by
  obtain ⟨δ,hδ,hh⟩ := C.exists_cycle_block_radius hnorm hstraight htrans
  refine ⟨δ,hδ,?_⟩
  intro ε hε hs d f hd hf N K hN hK hdi hfj
  let P := V.dartCycleChain d hd N hN
  let Q := C.shiftedCycleChain f hf K hK ε
  have hblocks (i j : ℕ) (hi : i < N) (hj : j < K) :=
    hh ε hε hs d f hd hf i j (hdi i hi) (hfj j hj)
  have hT : P.Transverse Q := by
    change (finitePolygonalChain Set.univ (V.dartCycleVertex d) (Set.mem_univ _) (V.dartCycleBlock d hd) N).Transverse
      (finitePolygonalChain Set.univ (C.shiftedCycleVertex f ε) (Set.mem_univ _) (C.shiftedCycleBlock f hf ε) K)
    apply finitePolygonalChain_transverse_left
    intro i hi
    apply finitePolygonalChain_transverse_right
    intro j hj
    exact (hblocks i j hi hj).1
  have hzero := P.closed_intersection_zero Q hT
  have hsplit : polygonIntersection P.vertices Q.vertices P.pieces Q.pieces=
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
        polygonIntersection (V.dartCycleBlock d hd i).vertices (C.shiftedCycleBlock f hf ε j).vertices
          (V.dartCycleBlock d hd i).pieces (C.shiftedCycleBlock f hf ε j).pieces :=
    finitePolygonalChain_intersection_double _ _ _ _ _ _ _ _
  rw [hsplit] at hzero
  calc
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
        polygonIntersection (V.dartCycleBlock d hd i).vertices (C.shiftedCycleBlock f hf ε j).vertices
          (V.dartCycleBlock d hd i).pieces (C.shiftedCycleBlock f hf ε j).pieces := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact (hblocks i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)).2.symm
    _ = 0 := hzero

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! The local pairing uses one fixed coordinate chart per vertex, including shared chord endpoints. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} [Fintype Vertex] [Fintype Edge] {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_vertex_pairing_radius (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∀ j k (a b : IncidentEdges graph j) (c d : IncidentEdges graph k), a ≠ b → c ≠ d →
        (polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain k c d t).vertices 1 1+
          polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain k c d (-t)).vertices 1 1)/2=
            C.vertexChordPairing j k a b c d := by
  obtain ⟨δ,hδ,-,hzero,havg⟩ := C.exists_vertex_chord_chain_radius hnorm
  refine ⟨δ,hδ,?_⟩
  intro t ht hs j k a b c d hab hcd
  by_cases h : k=j
  · subst k
    have hc : incidentCast (rfl : j=j) c=c := Subtype.ext rfl
    have hd : incidentCast (rfl : j=j) d=d := Subtype.ext rfl
    rw [vertexChordPairing,dite_eq_left rfl,hc,hd]
    exact havg t ht hs j a b c d hab hcd
  · have hzplus := hzero t (ne_of_gt ht) (by simpa only [abs_of_pos ht] using hs) j k (Ne.symm h) a b c d
    have hzminus := hzero (-t) (neg_ne_zero.mpr (ne_of_gt ht)) (by simpa only [abs_neg,abs_of_pos ht] using hs)
      j k (Ne.symm h) a b c d
    rw [hzplus,hzminus,zero_add,zero_div]
    simp only [vertexChordPairing,dite_eq_right h]

theorem exists_passage_pairing_radius (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∀ (d f : ℕ → OrientedDart graph)
        (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst) (i j : ℕ),
      OrientedDart.edge (d (i+1)) ≠ OrientedDart.edge (d i) →
      OrientedDart.edge (f (j+1)) ≠ OrientedDart.edge (f j) →
      (C.passageIntersection d f hd hf i j t+C.passageIntersection d f hd hf i j (-t))/2=
        C.passagePairing d f hd hf i j := by
  obtain ⟨δ,hδ,hh⟩ := C.exists_vertex_pairing_radius hnorm
  refine ⟨δ,hδ,?_⟩
  intro t ht hs d f hd hf i j hi hj
  exact hh t ht hs _ _ _ _ _ _ (dartPassage_ne d hd i hi) (dartPassage_ne f hf j hj)

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! Two actual physical shifts give the global averaged identity, with no restriction on shared edges between cycles. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} [Fintype Vertex] [Fintype Edge] {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
open scoped BigOperators
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem closed_cycle_averaged_sum (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (d f : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
    (N K : ℕ) (hN : d N=d 0) (hK : f K=f 0)
    (hdi : ∀ i, i < N → OrientedDart.edge (d (i+1)) ≠ OrientedDart.edge (d i))
    (hfj : ∀ j, j < K → OrientedDart.edge (f (j+1)) ≠ OrientedDart.edge (f j)) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
      (dartSign (d i)*dartSign (f j)*
        V.signedIntersection (OrientedDart.edge (d i)) (OrientedDart.edge (f j))+
          C.passagePairing d f hd hf i j)=0 := by
  obtain ⟨δ₀,hδ₀,hglobal⟩ := C.exists_closed_cycle_intersection_radius hnorm hstraight htrans
  obtain ⟨δ₁,hδ₁,hlocal⟩ := C.exists_passage_pairing_radius hnorm
  let t := min δ₀ δ₁/2
  have ht : 0 < t := half_pos (lt_min hδ₀ hδ₁)
  have htmin : t < min δ₀ δ₁ := half_lt_self (lt_min hδ₀ hδ₁)
  have ht₀ : t < δ₀ := htmin.trans_le (min_le_left _ _)
  have ht₁ : t < δ₁ := htmin.trans_le (min_le_right _ _)
  have hzplus := hglobal t (ne_of_gt ht) (by simpa only [abs_of_pos ht] using ht₀) d f hd hf N K hN hK hdi hfj
  have hzminus := hglobal (-t) (neg_ne_zero.mpr (ne_of_gt ht))
    (by simpa only [abs_neg,abs_of_pos ht] using ht₀) d f hd hf N K hN hK hdi hfj
  let E : ℕ → ℕ → ℝ := fun i j => dartSign (d i)*dartSign (f j)*
    V.signedIntersection (OrientedDart.edge (d i)) (OrientedDart.edge (f j))
  calc
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
        ((E i j+C.passageIntersection d f hd hf i j t)+
          (E i j+C.passageIntersection d f hd hf i j (-t)))/2 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [← hlocal t ht ht₁ d f hd hf i j (hdi i (Finset.mem_range.mp hi)) (hfj j (Finset.mem_range.mp hj))]
      dsimp only [E]
      ring
    _ = ((∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, (E i j+C.passageIntersection d f hd hf i j t))+
        (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, (E i j+C.passageIntersection d f hd hf i j (-t))))/2 := by
      simp only [div_eq_mul_inv,Finset.sum_add_distrib,Finset.sum_mul,add_mul]
    _ = 0 := by rw [hzplus,hzminus]; norm_num

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! Every local passage endpoint is counted once at the corresponding graph-edge endpoint. -/
noncomputable section
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.TruncatedSpokeCoordinates
open scoped BigOperators
variable {D : Paper170.AdmissibleDrawing graph} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem passage_sum_eq_endpoint_sum (d f : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
    (N K : ℕ) (hN : d N=d 0) (hK : f K=f 0) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, C.passagePairing d f hd hf i j)=
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
        dartSign (d i)*dartSign (f j)*
          C.edgeEndpointPairing (OrientedDart.edge (d i)) (OrientedDart.edge (f j)) := by
  have hTS := double_sum_cycle_shift_right d f N K hK
    (fun a b => C.flagPairing (dartTargetFlag a) (dartSourceFlag b))
  have hST := double_sum_cycle_shift_left d f N K hN
    (fun a b => C.flagPairing (dartSourceFlag a) (dartTargetFlag b))
  have hSS₀ := double_sum_cycle_shift_right (fun i => d (i+1)) f N K hK
    (fun a b => C.flagPairing (dartSourceFlag a) (dartSourceFlag b))
  have hSS₁ := double_sum_cycle_shift_left d f N K hN
    (fun a b => C.flagPairing (dartSourceFlag a) (dartSourceFlag b))
  simp_rw [C.passagePairing_flags,← C.dart_endpoint_pairing]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [hTS,hST,hSS₀,hSS₁]

def cycleIntersectionMatrix : Edge → Edge → ℝ :=
  fun e f => V.signedIntersection e f+C.edgeEndpointPairing e f

theorem closed_cycle_matrix_sum [Fintype Vertex] [Fintype Edge] (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (d f : ℕ → OrientedDart graph)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
    (N K : ℕ) (hN : d N=d 0) (hK : f K=f 0)
    (hdi : ∀ i, i < N → OrientedDart.edge (d (i+1)) ≠ OrientedDart.edge (d i))
    (hfj : ∀ j, j < K → OrientedDart.edge (f (j+1)) ≠ OrientedDart.edge (f j)) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
      dartSign (d i)*dartSign (f j)*
        C.cycleIntersectionMatrix (OrientedDart.edge (d i)) (OrientedDart.edge (f j))=0 := by
  have hh := C.closed_cycle_averaged_sum hnorm hstraight htrans d f hd hf N K hN hK hdi hfj
  simp only [Finset.sum_add_distrib] at hh
  rw [C.passage_sum_eq_endpoint_sum d f hd hf N K hN hK] at hh
  simpa only [cycleIntersectionMatrix,mul_add,Finset.sum_add_distrib] using hh

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

end OAI
