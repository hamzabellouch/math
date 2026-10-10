import OAI.Combinatorics.Crossing.ReducedPolygonalPresentation
import OAI.Combinatorics.Crossing.GraphWalkTrace

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem PolygonalChain.piece_subset_path_range {O : Set Plane} {a b : Plane}
    (P : PolygonalChain O a b) (i : ℕ) (hi : i < P.pieces) :
    segment ℝ (P.vertices i) (P.vertices (i+1)) ⊆ Set.range P.path := by
  exact polygonalArcPath_piece_subset_range P.vertices P.pieces i hi

theorem drawing_chain_range_eq {m n : ℕ} (D : ContinuousDrawing m n)
    (e : BipartiteEdge m n)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2))) :
    Set.range P.path=Set.range (D.edge e) :=
  path_range_eq_of_subset (D.edge e) P.path (D.edge_injective e) P.path_range_subset

theorem drawing_chain_pieces_pos {m n : ℕ} (D : ContinuousDrawing m n)
    (e : BipartiteEdge m n)
    (P : PolygonalChain (Set.range (D.edge e)) (D.vertex (.inl e.1)) (D.vertex (.inr e.2))) :
    0 < P.pieces := by
  apply P.pieces_pos_of_ne
  intro h
  cases D.vertex_injective h

end Zarankiewicz

end

end OAI
