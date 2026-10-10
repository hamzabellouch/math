import OAI.Combinatorics.Crossing.StraightChainTransversality
import OAI.Combinatorics.Crossing.UniformCrossTypeGeometry

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem chordChain_intersection (j k : BipartiteVertex m n) (a b : IncidentEdges j)
    (c d : IncidentEdges k) (ε : ℝ) :
    polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain k c d ε).vertices 1 1=
      segmentCrossingSign (V.spokePort j a) (V.spokePort j b) (C.shiftedPort k c ε) (C.shiftedPort k d ε) := by
  rw [VertexTruncation.chordChain,shiftedChordChain,PolygonalChain.intersection_single_single]

theorem exists_vertex_chord_chain_radius (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0<δ ∧
      (∀ ε : ℝ, ε ≠ 0 → |ε|<δ → ∀ j k (a b : IncidentEdges j) (c d : IncidentEdges k),
        a ≠ b → c ≠ d → (V.chordChain j a b).Transverse (C.shiftedChordChain k c d ε)) ∧
      (∀ ε : ℝ, ε ≠ 0 → |ε|<δ → ∀ j k, j ≠ k → ∀ (a b : IncidentEdges j) (c d : IncidentEdges k),
        polygonIntersection (V.chordChain j a b).vertices (C.shiftedChordChain k c d ε).vertices 1 1=0) ∧
      (∀ t : ℝ, 0<t → t<δ → ∀ j (a b c d : IncidentEdges j), a ≠ b → c ≠ d →
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

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
