import OAI.Combinatorics.Crossing.BipartiteDartGeometry
import OAI.Combinatorics.Crossing.PolygonalEndpointCasts

namespace OAI

noncomputable section
namespace Zarankiewicz
namespace VertexTruncation
variable {m n : ℕ} {D : ContinuousDrawing m n} (V : VertexTruncation D)

def dartTrackChain (d : (completeBipartite m n).Dart) :
    PolygonalChain Set.univ (V.spokePort d.fst (dartSourceIncident d))
      (V.spokePort d.snd (dartTargetIncident d)) := by
  rcases d with ⟨⟨u,v⟩,h⟩
  rcases u with i | p <;> rcases v with k | q
  · exact False.elim (by simp [completeBipartite,completeBipartiteGraph] at h)
  · exact (V.trackChain (i,q)).castEndpoints
      (by simp [spokePort,drawingSpokePort,dartSourceIncident,bipartiteDartEdge,startPort])
      (by simp [spokePort,drawingSpokePort,dartTargetIncident,bipartiteDartEdge,endPort])
  · exact (V.trackChain (k,p)).reverse.castEndpoints
      (by simp [spokePort,drawingSpokePort,dartSourceIncident,bipartiteDartEdge,endPort])
      (by simp [spokePort,drawingSpokePort,dartTargetIncident,bipartiteDartEdge,startPort])
  · exact False.elim (by simp [completeBipartite,completeBipartiteGraph] at h)

theorem dartTrackChain_forward_vertices (e : BipartiteEdge m n) :
    (V.dartTrackChain (forwardBipartiteDart e)).vertices=V.vertices e := rfl

theorem dartTrackChain_backward_vertices (e : BipartiteEdge m n) :
    (V.dartTrackChain (backwardBipartiteDart e)).vertices=reversedSequence (V.vertices e) (V.pieces e) := rfl

theorem dartTrackChain_pieces (d : (completeBipartite m n).Dart) :
    (V.dartTrackChain d).pieces=V.pieces (bipartiteDartEdge d) := by
  rcases bipartiteDart_cases d with ⟨e,rfl⟩ | ⟨e,rfl⟩ <;> rfl

end VertexTruncation
namespace TruncatedSpokeCoordinates
variable {m n : ℕ} {D : ContinuousDrawing m n} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

def shiftedDartChain (d : (completeBipartite m n).Dart) (ε : ℝ) :
    PolygonalChain Set.univ (C.shiftedPort d.fst (dartSourceIncident d) ε)
      (C.shiftedPort d.snd (dartTargetIncident d) ε) := by
  rcases d with ⟨⟨u,v⟩,h⟩
  rcases u with i | p <;> rcases v with k | q
  · exact False.elim (by simp [completeBipartite,completeBipartiteGraph] at h)
  · exact (C.shiftedEdgeChain (i,q) ε).castEndpoints rfl rfl
  · exact (C.shiftedEdgeChain (k,p) ε).reverse.castEndpoints rfl rfl
  · exact False.elim (by simp [completeBipartite,completeBipartiteGraph] at h)

theorem shiftedDartChain_forward_vertices (e : BipartiteEdge m n) (ε : ℝ) :
    (C.shiftedDartChain (forwardBipartiteDart e) ε).vertices=(C.shiftedEdgeChain e ε).vertices := rfl

theorem shiftedDartChain_backward_vertices (e : BipartiteEdge m n) (ε : ℝ) :
    (C.shiftedDartChain (backwardBipartiteDart e) ε).vertices=
      reversedSequence (C.shiftedEdgeChain e ε).vertices (C.shiftedEdgeChain e ε).pieces := rfl

theorem shiftedDartChain_pieces (d : (completeBipartite m n).Dart) (ε : ℝ) :
    (C.shiftedDartChain d ε).pieces=(C.shiftedEdgeChain (bipartiteDartEdge d) ε).pieces := by
  rcases bipartiteDart_cases d with ⟨e,rfl⟩ | ⟨e,rfl⟩ <;> rfl

end TruncatedSpokeCoordinates
end Zarankiewicz

end

end OAI
