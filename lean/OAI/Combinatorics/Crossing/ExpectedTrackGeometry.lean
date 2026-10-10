import OAI.Combinatorics.Crossing.UniformTrackPerturbation
import OAI.Combinatorics.Crossing.LocallyTransverseNormalization

namespace OAI

noncomputable section
namespace Zarankiewicz.ExpectedTrackGeometry

theorem actual_normalized_tracks {m n : ℕ} (D : AdmissibleDrawing m n) :
    ∃ A : AdmissibleDrawing m n,
      (crossingPoints A.toContinuousDrawing).ncard ≤ (crossingPoints D.toContinuousDrawing).ncard ∧
      ∃ V : VertexTruncation A.toContinuousDrawing,
        (∀ e, Function.Injective (V.path e)) ∧
        (∀ e f : BipartiteEdge m n, e ≠ f →
          Set.range (V.path e) ∩ Set.range (V.path f)=
            (A.edge e '' Set.Ioo (0 : unitInterval) 1) ∩ (A.edge f '' Set.Ioo (0 : unitInterval) 1)) ∧
        ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, ε ≠ 0 → |ε| < δ → ∀ e f : BipartiteEdge m n,
          polygonIntersection (V.vertices e) (shiftedTrack (V.vertices f) (V.pieces f) ε) (V.pieces e) (V.pieces f) =
            if e=f then 0 else polygonIntersection (V.vertices e) (V.vertices f) (V.pieces e) (V.pieces f) := by
  obtain ⟨A,hcount,hpoly,hnorm,hstraight,htrans⟩ := polygonal_no_adjacent_locally_transverse D
  obtain ⟨V⟩ := nonempty_vertexTruncation A.toContinuousDrawing hpoly
  refine ⟨A,?_,V,V.path_injective,?_,V.exists_uniform_track_intersections hnorm hstraight htrans⟩
  · simpa only [crossingCount,Set.ncard_eq_toFinset_card _ A.crossings_finite,
      Set.ncard_eq_toFinset_card _ D.crossings_finite] using hcount
  · intro e f hef
    exact V.edge_intersections_eq hnorm e f hef

end Zarankiewicz.ExpectedTrackGeometry

end

end OAI
