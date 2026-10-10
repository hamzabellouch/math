import OAI.Combinatorics.Crossing.TruncatedDrawingDisks
import OAI.Combinatorics.Crossing.IncidentSpokePorts

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem vertex_disks_crossing_free (D : AdmissibleDrawing m n) (hnorm : NoAdjacentCrossings D)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (r : ℝ)
    (hclear : ∀ j e (i : Fin (P e).pieces),
      ¬ ((j=Sum.inl e.1 ∧ i.val=0) ∨ (j=Sum.inr e.2 ∧ i.val+1=(P e).pieces)) →
      Disjoint (closedRoundDisk (D.vertex j) r) (segment ℝ ((P e).vertices i.val) ((P e).vertices (i.val+1))))
    (j : BipartiteVertex m n) :
    Disjoint (closedRoundDisk (D.vertex j) r) (crossingPoints D.toContinuousDrawing) := by
  apply Set.disjoint_left.mpr
  rintro x hxd ⟨e,f,hef,hxe,hxf⟩
  have hincident (g : BipartiteEdge m n) (hxg : x ∈ edgeInterior D.toContinuousDrawing g) :
      j=Sum.inl g.1 ∨ j=Sum.inr g.2 := by
    have hx := edgeInterior_subset_range D.toContinuousDrawing g hxg
    rw [← drawing_chain_range_eq D.toContinuousDrawing g (P g)] at hx
    obtain ⟨i,hi,hxi⟩ := polygonalArcPath_range_piece (P g).vertices (P g).pieces
      (drawing_chain_pieces_pos D.toContinuousDrawing g (P g)) x hx
    by_contra h
    have hbad : ¬ ((j=Sum.inl g.1 ∧ i=0) ∨ (j=Sum.inr g.2 ∧ i+1=(P g).pieces)) :=
      fun hh => h (hh.elim (fun hh => Or.inl hh.1) (fun hh => Or.inr hh.1))
    exact Set.disjoint_left.mp (hclear j g ⟨i,hi⟩ hbad) hxd hxi
  have hadj := incident_edges_adjacent j ⟨e,hincident e hxe⟩ ⟨f,hincident f hxf⟩
  have hh : x ∈ edgeInterior D.toContinuousDrawing e ∩ edgeInterior D.toContinuousDrawing f := ⟨hxe,hxf⟩
  rw [hnorm e f hef hadj] at hh
  exact hh

end Zarankiewicz

end

end OAI
