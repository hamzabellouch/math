import OAI.Combinatorics.Crossing.CycleEndpointSum
import OAI.Combinatorics.Crossing.WalkVectorSum

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem lemma3_1 (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    {u v : BipartiteVertex m n} (p : (completeBipartite m n).Walk u u)
    (q : (completeBipartite m n).Walk v v) (hp : p.IsCycle) (hq : q.IsCycle) :
    edgePairing C.cycleIntersectionMatrix (walkEdgeChain p) (walkEdgeChain q)=0 := by
  have hpl : 0 < p.length := by have := hp.three_le_length; omega
  have hql : 0 < q.length := by have := hq.three_le_length; omega
  rw [edgePairing_walk_dart_sum _ p q hpl hql]
  exact C.closed_cycle_matrix_sum hnorm hstraight htrans
    (cyclicWalkDart p hpl) (cyclicWalkDart q hql)
    (cyclicWalkDart_seam p hpl) (cyclicWalkDart_seam q hql) p.length q.length
    (cyclicWalkDart_period p hpl) (cyclicWalkDart_period q hql)
    (fun i _ => cyclicWalkDart_next_edge_ne p hp i) (fun j _ => cyclicWalkDart_next_edge_ne q hq j)

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
