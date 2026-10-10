import OAI.Combinatorics.Crossing.DartPathRealizations
import OAI.Combinatorics.Crossing.ShiftedEdgeIntersections
import OAI.Combinatorics.Crossing.ChordEdgeIntersections

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem dart_pair_intersection {ε : ℝ} (a b : (completeBipartite m n).Dart)
    (h : ∀ e f, (V.trackChain e).Transverse (C.shiftedEdgeChain f ε) ∧
      polygonIntersection (V.trackChain e).vertices (C.shiftedEdgeChain f ε).vertices
        (V.trackChain e).pieces (C.shiftedEdgeChain f ε).pieces=V.signedIntersection e f) :
    (V.dartTrackChain a).Transverse (C.shiftedDartChain b ε) ∧
      polygonIntersection (V.dartTrackChain a).vertices (C.shiftedDartChain b ε).vertices
        (V.dartTrackChain a).pieces (C.shiftedDartChain b ε).pieces=
          bipartiteDartSign a*bipartiteDartSign b*V.signedIntersection (bipartiteDartEdge a) (bipartiteDartEdge b) := by
  rcases bipartiteDart_cases a with ⟨e,rfl⟩ | ⟨e,rfl⟩ <;>
    rcases bipartiteDart_cases b with ⟨f,rfl⟩ | ⟨f,rfl⟩
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

theorem chord_dart_intersection {ε : ℝ} (j : BipartiteVertex m n) (a b : IncidentEdges j)
    (d : (completeBipartite m n).Dart)
    (h : ∀ e, (V.chordChain j a b).Transverse (C.shiftedEdgeChain e ε) ∧
      polygonIntersection (V.chordChain j a b).vertices (C.shiftedEdgeChain e ε).vertices
        (V.chordChain j a b).pieces (C.shiftedEdgeChain e ε).pieces=0) :
    (V.chordChain j a b).Transverse (C.shiftedDartChain d ε) ∧
      polygonIntersection (V.chordChain j a b).vertices (C.shiftedDartChain d ε).vertices
        (V.chordChain j a b).pieces (C.shiftedDartChain d ε).pieces=0 := by
  rcases bipartiteDart_cases d with ⟨e,rfl⟩ | ⟨e,rfl⟩
  · exact h e
  · obtain ⟨hT,hI⟩ := h e
    refine ⟨(V.chordChain j a b).transverse_reverse_right _ hT,?_⟩
    change polygonIntersection (V.chordChain j a b).vertices (C.shiftedEdgeChain e ε).reverse.vertices
      (V.chordChain j a b).pieces (C.shiftedEdgeChain e ε).reverse.pieces=0
    rw [PolygonalChain.intersection_reverse_right,hI,neg_zero]

theorem dart_chord_intersection {ε : ℝ} (j : BipartiteVertex m n) (a b : IncidentEdges j)
    (d : (completeBipartite m n).Dart)
    (h : ∀ e, (V.trackChain e).Transverse (C.shiftedChordChain j a b ε) ∧
      polygonIntersection (V.trackChain e).vertices (C.shiftedChordChain j a b ε).vertices
        (V.trackChain e).pieces (C.shiftedChordChain j a b ε).pieces=0) :
    (V.dartTrackChain d).Transverse (C.shiftedChordChain j a b ε) ∧
      polygonIntersection (V.dartTrackChain d).vertices (C.shiftedChordChain j a b ε).vertices
        (V.dartTrackChain d).pieces (C.shiftedChordChain j a b ε).pieces=0 := by
  rcases bipartiteDart_cases d with ⟨e,rfl⟩ | ⟨e,rfl⟩
  · exact h e
  · obtain ⟨hT,hI⟩ := h e
    refine ⟨(V.trackChain e).transverse_reverse_left _ hT,?_⟩
    change polygonIntersection (V.trackChain e).reverse.vertices (C.shiftedChordChain j a b ε).vertices
      (V.trackChain e).reverse.pieces (C.shiftedChordChain j a b ε).pieces=0
    rw [PolygonalChain.intersection_reverse_left,hI,neg_zero]

theorem exists_dart_intersection_radius (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε| < δ →
      (∀ a b : (completeBipartite m n).Dart,
        (V.dartTrackChain a).Transverse (C.shiftedDartChain b ε) ∧
        polygonIntersection (V.dartTrackChain a).vertices (C.shiftedDartChain b ε).vertices
          (V.dartTrackChain a).pieces (C.shiftedDartChain b ε).pieces=
            bipartiteDartSign a*bipartiteDartSign b*V.signedIntersection (bipartiteDartEdge a) (bipartiteDartEdge b)) ∧
      (∀ j (a b : IncidentEdges j) d,
        (V.chordChain j a b).Transverse (C.shiftedDartChain d ε) ∧
        polygonIntersection (V.chordChain j a b).vertices (C.shiftedDartChain d ε).vertices
          (V.chordChain j a b).pieces (C.shiftedDartChain d ε).pieces=0) ∧
      (∀ j (a b : IncidentEdges j) d,
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

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
