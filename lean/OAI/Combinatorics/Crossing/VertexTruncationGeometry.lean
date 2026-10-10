import OAI.Combinatorics.Crossing.VertexTruncation

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
variable {m n : ℕ}

theorem offset_avoidance {D : ContinuousDrawing m n} (V : VertexTruncation D) (e : BipartiteEdge m n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ≠ 0 → |t| < δ → ∀ i j : Fin (V.pieces e),
      ¬ ClosedSegmentsMeet (V.vertices e i.val) (V.vertices e (i.val+1))
        (shiftedTrack (V.vertices e) (V.pieces e) t j.val)
        (shiftedTrack (V.vertices e) (V.pieces e) t (j.val+1)) :=
  (V.chain e).truncated_offset_avoidance (V.minimal e) V.radius V.radius_pos (V.short e).1 (V.short e).2

theorem edge_intersections_eq {D : AdmissibleDrawing m n} (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (e f : BipartiteEdge m n) (hef : e ≠ f) :
    Set.range (V.path e) ∩ Set.range (V.path f)=edgeInterior D.toContinuousDrawing e ∩ edgeInterior D.toContinuousDrawing f :=
  truncated_edge_intersections_eq D hnorm V.chain V.minimal V.radius V.radius_pos V.short V.piece_clearance e f hef

theorem pair_transverse {D : AdmissibleDrawing m n} (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (e f : BipartiteEdge m n) (hef : e ≠ f) (i : Fin (V.pieces e)) (j : Fin (V.pieces f)) :
    SegmentPairTransverse (V.vertices e i.val) (V.vertices e (i.val+1))
      (V.vertices f j.val) (V.vertices f (j.val+1)) :=
  truncated_segment_pair_transverse D hnorm hstraight htrans V.chain V.minimal V.radius V.radius_pos
    V.short V.piece_clearance e f hef i j

theorem crossing_free_disks {D : AdmissibleDrawing m n} (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (j : BipartiteVertex m n) :
    Disjoint (closedRoundDisk (D.vertex j) V.radius) (crossingPoints D.toContinuousDrawing) :=
  vertex_disks_crossing_free D hnorm V.chain V.radius V.piece_clearance j

theorem vertices_not_crossing {D : AdmissibleDrawing m n} (V : VertexTruncation D.toContinuousDrawing)
    (hnorm : NoAdjacentCrossings D) (hstraight : LocallyStraightCrossings D)
    (e : BipartiteEdge m n) (i : ℕ) (hi : i ≤ V.pieces e) : V.vertices e i ∉ crossingPoints D.toContinuousDrawing :=
  truncated_vertices_not_crossing D hnorm hstraight V.chain V.minimal V.radius V.piece_clearance e i hi

theorem vertex_disk_cases {D : ContinuousDrawing m n} (V : VertexTruncation D)
    (j : BipartiteVertex m n) (e : BipartiteEdge m n) (x : Plane) (hx : x ∈ Set.range (V.path e)) :
    (j=Sum.inl e.1 ∧ x=V.startPort e) ∨ (j=Sum.inr e.2 ∧ x=V.endPort e) ∨
      V.radius^2 < squaredLength (x-D.vertex j) :=
  truncated_path_vertex_disk_cases D V.chain V.minimal V.radius V.radius_pos V.short V.piece_clearance j e x hx

end Zarankiewicz.VertexTruncation

end

end OAI
