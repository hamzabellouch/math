import OAI.Combinatorics.Crossing.StraightChainTransversality
import OAI.Combinatorics.Crossing.UniformCrossTypeGeometry

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_chord_edge_radius (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ →
      (∀ j (a b : IncidentEdges j) e,
        (V.chordChain j a b).Transverse (C.shiftedEdgeChain e ε) ∧
        polygonIntersection (V.chordChain j a b).vertices (C.shiftedEdgeChain e ε).vertices
          (V.chordChain j a b).pieces (C.shiftedEdgeChain e ε).pieces=0) ∧
      (∀ j (a b : IncidentEdges j) e,
        (V.trackChain e).Transverse (C.shiftedChordChain j a b ε) ∧
        polygonIntersection (V.trackChain e).vertices (C.shiftedChordChain j a b ε).vertices
          (V.trackChain e).pieces (C.shiftedChordChain j a b ε).pieces=0) := by
  obtain ⟨δ,hδ,hh⟩ := C.exists_cross_type_radius hnorm
  refine ⟨δ,hδ,?_⟩
  intro ε hε hsmall
  obtain ⟨hTC,hTChord,hChordT,hChordC,hChordChord,hOther⟩ := hh ε hε hsmall
  constructor
  · intro j a b e
    have hconn (k : BipartiteVertex m n) (f : IncidentEdges k) :
        (V.chordChain j a b).Transverse (C.connectorChain k f ε) := by
      apply PolygonalChain.transverse_single_single
      exact segmentPairTransverse_of_not_meet _ _ _ _ (hChordC j k a b f)
    have hmid : (V.chordChain j a b).Transverse (C.shiftedTrackChain e ε) := by
      apply PolygonalChain.transverse_single_left
      intro i
      exact segmentPairTransverse_of_not_meet _ _ _ _ (hChordT j a b e i)
    have hzconn (k : BipartiteVertex m n) (f : IncidentEdges k) :
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
        (((C.connectorChain (Sum.inl e.1) (V.leftIncident e) ε).join (C.shiftedTrackChain e ε)).join
          (C.connectorChain (Sum.inr e.2) (V.rightIncident e) ε).reverse)
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

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
