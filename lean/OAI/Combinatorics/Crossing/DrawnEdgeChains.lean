import OAI.Combinatorics.Crossing.FinitePolygonalComposition
import OAI.Combinatorics.Crossing.TrackEndpointConnections

namespace OAI

noncomputable section
namespace Zarankiewicz
namespace VertexTruncation
variable {m n : ℕ} {D : ContinuousDrawing m n} (V : VertexTruncation D)

def trackChain (e : BipartiteEdge m n) : PolygonalChain Set.univ (V.startPort e) (V.endPort e) where
  pieces := V.pieces e
  vertices := V.vertices e
  first := V.vertices_first e
  last := V.vertices_last e
  start_mem := Set.mem_univ _
  inside := fun _ _ => Set.subset_univ _

def chordChain (j : BipartiteVertex m n) (a b : IncidentEdges j) :
    PolygonalChain Set.univ (V.spokePort j a) (V.spokePort j b) :=
  PolygonalChain.single Set.univ _ _ (Set.mem_univ _) (Set.subset_univ _)

end VertexTruncation
namespace TruncatedSpokeCoordinates
variable {m n : ℕ} {D : ContinuousDrawing m n} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

def shiftedTrackChain (e : BipartiteEdge m n) (ε : ℝ) :
    PolygonalChain Set.univ (C.tangentPort (Sum.inl e.1) (V.leftIncident e) ε)
      (C.tangentPort (Sum.inr e.2) (V.rightIncident e) ε) where
  pieces := V.pieces e
  vertices := shiftedTrack (V.vertices e) (V.pieces e) ε
  first := V.shiftedTrack_first C e ε
  last := V.shiftedTrack_last C e ε
  start_mem := Set.mem_univ _
  inside := fun _ _ => Set.subset_univ _

def connectorChain (j : BipartiteVertex m n) (e : IncidentEdges j) (ε : ℝ) :
    PolygonalChain Set.univ (C.shiftedPort j e ε) (C.tangentPort j e ε) :=
  PolygonalChain.single Set.univ _ _ (Set.mem_univ _) (Set.subset_univ _)

def shiftedEdgeChain (e : BipartiteEdge m n) (ε : ℝ) :
    PolygonalChain Set.univ (C.shiftedPort (Sum.inl e.1) (V.leftIncident e) ε)
      (C.shiftedPort (Sum.inr e.2) (V.rightIncident e) ε) :=
  ((C.connectorChain (Sum.inl e.1) (V.leftIncident e) ε).join (C.shiftedTrackChain e ε)).join
    (C.connectorChain (Sum.inr e.2) (V.rightIncident e) ε).reverse

def shiftedChordChain (j : BipartiteVertex m n) (a b : IncidentEdges j) (ε : ℝ) :
    PolygonalChain Set.univ (C.shiftedPort j a ε) (C.shiftedPort j b ε) :=
  PolygonalChain.single Set.univ _ _ (Set.mem_univ _) (Set.subset_univ _)

theorem shiftedEdgeChain_pieces (e : BipartiteEdge m n) (ε : ℝ) :
    (C.shiftedEdgeChain e ε).pieces=V.pieces e+2 := by
  simp only [shiftedEdgeChain,PolygonalChain.pieces_join,connectorChain,
    PolygonalChain.pieces_single,shiftedTrackChain,PolygonalChain.reverse]
  omega

theorem shiftedEdgeChain_intersection_right (e : BipartiteEdge m n) (ε : ℝ)
    (w : ℕ → Plane) (k : ℕ) :
    polygonIntersection w (C.shiftedEdgeChain e ε).vertices k (C.shiftedEdgeChain e ε).pieces =
      polygonIntersection w (C.connectorChain (Sum.inl e.1) (V.leftIncident e) ε).vertices k 1 +
      polygonIntersection w (shiftedTrack (V.vertices e) (V.pieces e) ε) k (V.pieces e) -
      polygonIntersection w (C.connectorChain (Sum.inr e.2) (V.rightIncident e) ε).vertices k 1 := by
  unfold shiftedEdgeChain
  rw [PolygonalChain.intersection_join_right,PolygonalChain.intersection_join_right,
    PolygonalChain.intersection_reverse_right]
  rfl

end TruncatedSpokeCoordinates
end Zarankiewicz

end

end OAI
