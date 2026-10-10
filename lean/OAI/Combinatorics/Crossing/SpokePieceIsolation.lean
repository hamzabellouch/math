import OAI.Combinatorics.Crossing.TruncatedSignedIntersections
import OAI.Combinatorics.Crossing.TrackEndpointConnections

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
variable {m n : ℕ}

theorem spokePort_interior {D : ContinuousDrawing m n} (V : VertexTruncation D)
    (j : BipartiteVertex m n) (f : IncidentEdges j) : V.spokePort j f ∈ edgeInterior D f.val :=
  drawingSpokePort_interior D V.chain V.minimal V.radius V.radius_pos V.weak_short j f

theorem spokePort_piece_unique {D : AdmissibleDrawing m n} (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (j : BipartiteVertex m n) (f : IncidentEdges j)
    (e : BipartiteEdge m n) (i : Fin (V.pieces e))
    (hx : V.spokePort j f ∈ segment ℝ (V.vertices e i.val) (V.vertices e (i.val+1))) :
    e=f.val ∧ i.val=V.spokeIndex j f := by
  have hcircle : V.spokePort j f ∈ closedRoundDisk (D.vertex j) V.radius := by
    change squaredLength (V.spokePort j f-D.vertex j) ≤ V.radius^2
    rw [V.spokePort_circle]
  have he : e=f.val := by
    by_contra hef
    have hcross : V.spokePort j f ∈ crossingPoints D.toContinuousDrawing :=
      ⟨e,f.val,hef,V.range_subset_edgeInterior e (V.piece_subset_range e i.val i.isLt hx),V.spokePort_interior j f⟩
    exact Set.disjoint_left.mp (V.crossing_free_disks hnorm j) hcircle hcross
  have hcase : (j=Sum.inl e.1 ∧ i.val=0) ∨ (j=Sum.inr e.2 ∧ i.val+1=V.pieces e) := by
    by_contra hh
    have hold := (V.chain e).truncated_piece_subset V.radius V.radius_pos
      (V.weak_short e).1 (V.weak_short e).2 i.val i.isLt hx
    exact Set.disjoint_left.mp (V.piece_clearance j e i hh) hcircle hold
  refine ⟨he,?_⟩
  unfold spokeIndex
  split_ifs with hj
  · rcases hcase with hh | hh
    · exact hh.2
    · have hbad : Sum.inl f.val.1=Sum.inr e.2 := hj.symm.trans hh.1
      cases hbad
  · rcases hcase with hh | hh
    · exact False.elim (hj (hh.1.trans (congrArg (fun g : BipartiteEdge m n => Sum.inl g.1) he)))
    · have hn : V.pieces e=V.pieces f.val := congrArg V.pieces he
      omega

end Zarankiewicz.VertexTruncation

end

end OAI
