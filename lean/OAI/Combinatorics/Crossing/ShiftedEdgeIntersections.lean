import OAI.Combinatorics.Crossing.StraightChainIntersections
import OAI.Combinatorics.Crossing.ConnectorTrackAvoidance

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_complete_edge_intersection_radius (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ → ∀ e f : BipartiteEdge m n,
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
  have hconn (j : BipartiteVertex m n) (g : IncidentEdges j) :
      (V.trackChain e).Transverse (C.connectorChain j g ε) := by
    apply PolygonalChain.transverse_single_right
    intro i
    exact segmentPairTransverse_of_not_meet _ _ _ _ (hC ε hε (hsmall.trans_le hb₂) j g e i)
  have hmid : (V.trackChain e).Transverse (C.shiftedTrackChain f ε) := by
    intro i j
    exact (hT ε hε (hsmall.trans_le hb₀) e f i j).1
  have hzero (j : BipartiteVertex m n) (g : IncidentEdges j) :
      polygonIntersection (V.trackChain e).vertices (C.connectorChain j g ε).vertices (V.trackChain e).pieces 1=0 := by
    apply PolygonalChain.intersection_single_right_zero
    intro i
    exact hC ε hε (hsmall.trans_le hb₂) j g e i
  constructor
  · change (V.trackChain e).Transverse
      (((C.connectorChain (Sum.inl f.1) (V.leftIncident f) ε).join (C.shiftedTrackChain f ε)).join
        (C.connectorChain (Sum.inr f.2) (V.rightIncident f) ε).reverse)
    apply PolygonalChain.transverse_join_right
    · exact PolygonalChain.transverse_join_right _ _ _ (hconn _ _) hmid
    · exact (V.trackChain e).transverse_reverse_right _ (hconn _ _)
  · rw [C.shiftedEdgeChain_intersection_right,hzero,hzero,zero_add,sub_zero]
    exact hI ε hε (hsmall.trans_le hb₁) e f

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
