import OAI.Combinatorics.Crossing.RoundDiskChords
import OAI.Combinatorics.Crossing.PhysicalVertexChords
import OAI.Combinatorics.Crossing.SpokePieceIsolation

namespace OAI

noncomputable section
namespace Zarankiewicz
namespace VertexTruncation
variable {m n : ℕ} {D : ContinuousDrawing m n} (V : VertexTruncation D)

theorem track_in_disk_is_port (j : BipartiteVertex m n) (e : BipartiteEdge m n) (x : Plane)
    (hx : x ∈ Set.range (V.path e)) (hmem : x ∈ closedRoundDisk (D.vertex j) V.radius) :
    ∃ f : IncidentEdges j, x=V.spokePort j f := by
  rcases V.vertex_disk_cases j e x hx with ⟨hj,he⟩ | ⟨hj,he⟩ | hout
  · refine ⟨⟨e,Or.inl hj⟩,?_⟩
    simpa only [spokePort,drawingSpokePort,ite_eq_left hj,startPort] using he
  · have hnot : j ≠ Sum.inl e.1 := by
      intro hh
      cases hh.symm.trans hj
    refine ⟨⟨e,Or.inr hj⟩,?_⟩
    simpa only [spokePort,drawingSpokePort,ite_eq_right hnot,endPort] using he
  · exact False.elim (not_lt_of_ge hmem hout)

end VertexTruncation
namespace TruncatedSpokeCoordinates
variable {m n : ℕ} {D : ContinuousDrawing m n} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem track_shifted_chord_disjoint (j : BipartiteVertex m n) (c d : IncidentEdges j)
    (ε : ℝ) (hc : |V.spokeScale j c*ε|≤1) (hd : |V.spokeScale j d*ε|≤1)
    (hsep : ∀ f g : IncidentEdges j, V.spokePort j f ≠ C.shiftedPort j g ε)
    (e : BipartiteEdge m n) (i : Fin (V.pieces e)) :
    ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
      (C.shiftedPort j c ε) (C.shiftedPort j d ε) := by
  intro hmeet
  obtain ⟨x,hx,hy⟩ := (closedSegmentsMeet_iff_nonempty_inter _ _ _ _).mp hmeet
  have hcirclec := C.shiftedPort_circle j c ε hc
  have hcircled := C.shiftedPort_circle j d ε hd
  have hmem := round_chord_subset_closed_disk (D.vertex j) _ _ V.radius hcirclec hcircled hy
  obtain ⟨f,hf⟩ := V.track_in_disk_is_port j e x (V.piece_subset_range e i.val i.isLt hx) hmem
  have hboundary : squaredLength (x-D.vertex j)=V.radius^2 := by rw [hf,V.spokePort_circle]
  rcases round_chord_boundary_endpoints (D.vertex j) _ _ x V.radius hcirclec hcircled hy hboundary with h | h
  · exact hsep f c (hf.symm.trans h)
  · exact hsep f d (hf.symm.trans h)

end TruncatedSpokeCoordinates
end Zarankiewicz

end

end OAI
