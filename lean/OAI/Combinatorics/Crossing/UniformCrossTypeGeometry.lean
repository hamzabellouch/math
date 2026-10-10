import OAI.Combinatorics.Crossing.ChordExteriorSeparation
import OAI.Combinatorics.Crossing.ConnectorTrackAvoidance
import OAI.Combinatorics.Crossing.SegmentTraversalReversal

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem exists_cross_type_radius (hnorm : NoAdjacentCrossings D) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε|<δ →
      (∀ j (f : IncidentEdges j) e (i : Fin (V.pieces e)),
        ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
          (C.shiftedPort j f ε) (C.tangentPort j f ε)) ∧
      (∀ j (c d : IncidentEdges j) e (i : Fin (V.pieces e)),
        ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
          (C.shiftedPort j c ε) (C.shiftedPort j d ε)) ∧
      (∀ j (a b : IncidentEdges j) e (i : Fin (V.pieces e)),
        ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b)
          (shiftedTrack (V.vertices e) (V.pieces e) ε i.val)
          (shiftedTrack (V.vertices e) (V.pieces e) ε (i.val+1))) ∧
      (∀ j k (a b : IncidentEdges j) (f : IncidentEdges k),
        ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b)
          (C.shiftedPort k f ε) (C.tangentPort k f ε)) ∧
      (∀ j k (a b : IncidentEdges j) (c d : IncidentEdges k), a ≠ b → c ≠ d →
        SegmentPairTransverse (V.spokePort j a) (V.spokePort j b) (C.shiftedPort k c ε) (C.shiftedPort k d ε)) ∧
      (∀ j k, j ≠ k → ∀ (a b : IncidentEdges j) (c d : IncidentEdges k),
        ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b) (C.shiftedPort k c ε) (C.shiftedPort k d ε)) := by
  obtain ⟨δ₀,hδ₀,htracks⟩ := V.exists_all_vertex_disk_radius
  obtain ⟨δ₁,hδ₁,hconnectors⟩ := C.exists_all_connector_track_radius hnorm
  obtain ⟨δ₂,hδ₂,hother⟩ := C.exists_connector_other_disks_radius
  obtain ⟨δ₃,hδ₃,hseparate⟩ := C.exists_uniform_endpoint_radius
  obtain ⟨δ₄,hδ₄,hscale⟩ := C.exists_uniform_scale_radius
  let δ := min δ₀ (min δ₁ (min δ₂ (min δ₃ δ₄)))
  have hδ : 0<δ := lt_min hδ₀ (lt_min hδ₁ (lt_min hδ₂ (lt_min hδ₃ hδ₄)))
  have hb₀ : δ≤δ₀ := min_le_left _ _
  have hb₁ : δ≤δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hb₂ : δ≤δ₂ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb₃ : δ≤δ₃ := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hb₄ : δ≤δ₄ := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨δ,hδ,?_⟩
  intro ε hε hsmall
  have hs := hscale ε (hsmall.trans_le hb₄)
  have hsep := hseparate ε hε (hsmall.trans_le hb₃)
  refine ⟨hconnectors ε hε (hsmall.trans_le hb₁),?_,?_,?_,?_,?_⟩
  · intro j c d e i
    exact C.track_shifted_chord_disjoint j c d ε (hs j c).le (hs j d).le (hsep j).1 e i
  · intro j a b e i
    exact round_chord_exterior_disjoint (D.vertex j) _ _ _ _ V.radius
      (V.spokePort_circle j a) (V.spokePort_circle j b) (htracks ε hε (hsmall.trans_le hb₀) j e i)
  · intro j k a b f
    by_cases hjk : j=k
    · subst k
      exact C.chord_connector_disjoint_all_passages j a b f ε hε (hs j f) ((hsep j).1 a f) ((hsep j).1 b f)
    · exact round_chord_exterior_disjoint (D.vertex j) _ _ _ _ V.radius
        (V.spokePort_circle j a) (V.spokePort_circle j b)
        (hother ε (hsmall.trans_le hb₂) k j (Ne.symm hjk) f)
  · intro j k a b c d hab hcd
    by_cases hjk : j=k
    · subst k
      exact C.shifted_chords_transverse j a b c d ε (fun e => (hs j e).le) (hsep j).1 (hsep j).2 hab hcd
    · exact segmentPairTransverse_of_not_meet _ _ _ _
        (C.different_vertex_chords_disjoint j k hjk a b c d ε (hs k c).le (hs k d).le)
  · intro j k hjk a b c d
    exact C.different_vertex_chords_disjoint j k hjk a b c d ε (hs k c).le (hs k d).le

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
