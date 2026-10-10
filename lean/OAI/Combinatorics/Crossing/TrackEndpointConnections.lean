import OAI.Combinatorics.Crossing.TruncatedSpokeCoordinates

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
variable {m n : ℕ} {D : ContinuousDrawing m n} (V : VertexTruncation D)

def leftIncident (_V : VertexTruncation D) (e : BipartiteEdge m n) : IncidentEdges (m:=m) (n:=n) (Sum.inl e.1) := ⟨e,Or.inl rfl⟩
def rightIncident (_V : VertexTruncation D) (e : BipartiteEdge m n) : IncidentEdges (m:=m) (n:=n) (Sum.inr e.2) := ⟨e,Or.inr rfl⟩

theorem vertices_first (e : BipartiteEdge m n) : V.vertices e 0=V.startPort e :=
  (V.chain e).truncatedVertices_first V.radius

theorem vertices_last (e : BipartiteEdge m n) : V.vertices e (V.pieces e)=V.endPort e :=
  (V.chain e).truncatedVertices_last (V.pieces_pos e) V.radius

theorem spokePort_left (e : BipartiteEdge m n) :
    V.spokePort (Sum.inl e.1) (V.leftIncident e)=V.startPort e := by
  simp [spokePort,drawingSpokePort,leftIncident,startPort]

theorem spokePort_right (e : BipartiteEdge m n) :
    V.spokePort (Sum.inr e.2) (V.rightIncident e)=V.endPort e := by
  simp [spokePort,drawingSpokePort,rightIncident,endPort]

theorem shiftedTrack_first (C : TruncatedSpokeCoordinates V) (e : BipartiteEdge m n) (ε : ℝ) :
    shiftedTrack (V.vertices e) (V.pieces e) ε 0=
      C.tangentPort (Sum.inl e.1) (V.leftIncident e) ε := by
  simp [shiftedTrack,trackOffset,TruncatedSpokeCoordinates.tangentPort,spokeDirection,
    spokeIndex,leftIncident,V.vertices_first,spokePort,drawingSpokePort,startPort]

theorem shiftedTrack_last (C : TruncatedSpokeCoordinates V) (e : BipartiteEdge m n) (ε : ℝ) :
    shiftedTrack (V.vertices e) (V.pieces e) ε (V.pieces e)=
      C.tangentPort (Sum.inr e.2) (V.rightIncident e) ε := by
  have hn : V.pieces e ≠ 0 := ne_of_gt (V.pieces_pos e)
  simp [shiftedTrack,trackOffset,hn,TruncatedSpokeCoordinates.tangentPort,spokeDirection,
    spokeIndex,rightIncident,V.vertices_last,spokePort,drawingSpokePort,endPort]

end Zarankiewicz.VertexTruncation

end

end OAI
