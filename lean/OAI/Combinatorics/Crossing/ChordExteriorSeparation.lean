import OAI.Combinatorics.Crossing.TrackChordSeparation
import OAI.Combinatorics.Crossing.ConnectorOtherDisks
import OAI.Combinatorics.Crossing.ShiftedTrackDisks

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem round_chord_exterior_disjoint (z a b c d : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (hout : segment ℝ c d ⊆ {x | r^2 < squaredLength (x-z)}) : ¬ ClosedSegmentsMeet a b c d := by
  intro hh
  obtain ⟨x,hx,hy⟩ := (closedSegmentsMeet_iff_nonempty_inter _ _ _ _).mp hh
  have hle := round_chord_subset_closed_disk z a b r ha hb hx
  have hlt : r^2 < squaredLength (x-z) := hout hy
  change squaredLength (x-z) ≤ r^2 at hle
  exact not_lt_of_ge hle hlt

namespace TruncatedSpokeCoordinates
variable {m n : ℕ} {D : ContinuousDrawing m n} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem different_vertex_chords_disjoint (j k : BipartiteVertex m n) (hjk : j ≠ k)
    (a b : IncidentEdges j) (c d : IncidentEdges k) (ε : ℝ)
    (hc : |V.spokeScale k c*ε|≤1) (hd : |V.spokeScale k d*ε|≤1) :
    ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b) (C.shiftedPort k c ε) (C.shiftedPort k d ε) := by
  apply not_closedSegmentsMeet_of_disjoint
  exact (V.disks_disjoint j k hjk).mono
    (round_chord_subset_closed_disk _ _ _ _ (V.spokePort_circle j a) (V.spokePort_circle j b))
    (round_chord_subset_closed_disk _ _ _ _ (C.shiftedPort_circle k c ε hc) (C.shiftedPort_circle k d ε hd))

theorem chord_connector_disjoint_all_passages (j : BipartiteVertex m n) (a b f : IncidentEdges j)
    (ε : ℝ) (hne : ε ≠ 0) (hsmall : |V.spokeScale j f*ε|<1)
    (ha : V.spokePort j a ≠ C.shiftedPort j f ε) (hb : V.spokePort j b ≠ C.shiftedPort j f ε) :
    ¬ ClosedSegmentsMeet (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j f ε) (C.tangentPort j f ε) := by
  rintro ⟨s,hs,t,ht,he⟩
  have hx : segmentPoint (V.spokePort j a) (V.spokePort j b) s ∈ segment ℝ (V.spokePort j a) (V.spokePort j b) := by
    rw [← Path.range_segment]
    exact ⟨⟨s,hs⟩,by simp only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint]⟩
  have hinside := round_chord_subset_closed_disk (D.vertex j) _ _ V.radius
    (V.spokePort_circle j a) (V.spokePort_circle j b) hx
  by_cases htp : 0<t
  · have hout := C.connector_strictly_outside j f ε hsmall hne t htp
    rw [← he] at hout
    exact not_lt_of_ge hinside hout
  · have ht0 : t=0 := by linarith [ht.1]
    rw [ht0,segmentPoint_zero] at he
    have hboundary : squaredLength (segmentPoint (V.spokePort j a) (V.spokePort j b) s-D.vertex j)=V.radius^2 := by
      rw [he]
      exact C.shiftedPort_circle j f ε hsmall.le
    rcases round_chord_boundary_endpoints (D.vertex j) _ _ _ V.radius
      (V.spokePort_circle j a) (V.spokePort_circle j b) hx hboundary with h | h
    · exact ha (h.symm.trans he)
    · exact hb (h.symm.trans he)

end TruncatedSpokeCoordinates
end Zarankiewicz

end

end OAI
