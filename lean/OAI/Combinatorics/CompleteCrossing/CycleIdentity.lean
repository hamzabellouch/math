import OAI.Combinatorics.CompleteCrossing.CycleIntersections
import OAI.Combinatorics.CompleteCrossing.Refinement
import OAI.Combinatorics.CompleteCrossing.Tensor

namespace OAI

/-! The geometric cycle identity deduced from endpoint and intersection coordinates. -/

section

/-! Actual vertex-coordinate orders give the frozen signed endpoint contribution. -/
noncomputable section
open scoped BigOperators Classical
namespace Paper170
variable {Vertex Edge : Type} {graph : Graph Vertex Edge}

theorem endpointSign_eq_sub_indicators (v : Vertex) (e : Edge) :
    endpointSign graph v e =
      (if graph.src e=v then 1 else 0) - (if graph.dst e=v then 1 else 0) := by
  by_cases hs : graph.src e=v
  · have ht : graph.dst e≠v := fun h => graph.loopless e (hs.trans h.symm)
    simp [endpointSign,hs,ht]
  · by_cases ht : graph.dst e=v <;> simp [endpointSign,hs,ht]

theorem sum_endpointSign [Fintype Vertex] (e : Edge) (f : Vertex → ℝ) :
    (∑v, endpointSign graph v e * f v) = f (graph.src e)-f (graph.dst e) := by
  simp [endpointSign_eq_sub_indicators,sub_mul,ite_mul,Finset.sum_sub_distrib]

end Paper170

namespace Paper170Geometry.TruncatedSpokeCoordinates
open Zarankiewicz
variable {Vertex Edge : Type} [Fintype Vertex] {graph : Paper170.Graph Vertex Edge}
  {N : Paper170.NormalizedDrawing graph} {V : VertexTruncation N.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V) (O : Paper170.SpokeOrders N)

omit [Fintype Vertex] in
theorem flagPairing_eq_spokeComparison
    (hnode : ∀v (e f : IncidentEdges graph v),
      orderSign (C.node v e) (C.node v f) = Paper170.spokeComparison O v e.val f.val)
    (a b : IncidentFlag graph) : C.flagPairing a b =
      if b.1=a.1 then Paper170.spokeComparison O a.1 a.2.val b.2.val / 2 else 0 := by
  unfold flagPairing
  split_ifs with h
  · rw [hnode]
    rfl
  · rfl

theorem edgeEndpointPairing_eq_signed_sum
    (hnode : ∀v (e f : IncidentEdges graph v),
      orderSign (C.node v e) (C.node v f) = Paper170.spokeComparison O v e.val f.val)
    (e f : Edge) : C.edgeEndpointPairing e f =
      (1/2 : ℝ) * ∑v, Paper170.endpointSign graph v e * Paper170.endpointSign graph v f *
        Paper170.spokeComparison O v e f := by
  have hsum := Paper170.sum_endpointSign (graph := graph) e
    (fun v => Paper170.endpointSign graph v f * Paper170.spokeComparison O v e f)
  simp only [← mul_assoc] at hsum
  rw [hsum]
  unfold edgeEndpointPairing
  rw [C.flagPairing_eq_spokeComparison O hnode,C.flagPairing_eq_spokeComparison O hnode,
    C.flagPairing_eq_spokeComparison O hnode,C.flagPairing_eq_spokeComparison O hnode]
  simp only [dartSourceFlag,dartTargetFlag,dartSourceIncident,dartTargetIncident,
    forwardDart,OrientedDart.fst,OrientedDart.snd,Paper170.endpointSign_eq_sub_indicators]
  split_ifs <;> ring

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! The geometric closed-polygon calculation annihilates the real graph cycle space. -/
noncomputable section
namespace Paper170Geometry.TruncatedSpokeCoordinates
variable {Vertex Edge : Type} [Fintype Vertex] [Fintype Edge]
  {graph : Paper170.Graph Vertex Edge} {D : Paper170.AdmissibleDrawing graph}
  {V : VertexTruncation D.toContinuousDrawing} (C : TruncatedSpokeCoordinates V)

theorem cycleMatrix_pairing_zero (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (z z' : Edge → ℝ) (hz : ∀v, Paper170.boundary graph z v = 0)
    (hz' : ∀v, Paper170.boundary graph z' v = 0) :
    Paper170.edgePairing C.cycleIntersectionMatrix z z' = 0 := by
  apply Paper170.edgePairing_eq_zero_of_simple_cycles graph C.cycleIntersectionMatrix ?_ z z' hz hz'
  intro P Q
  rw [Paper170.edgePairing_simple_cycles_range]
  exact C.closed_cycle_matrix_sum hnorm hstraight htrans P.cyclicDart Q.cyclicDart
    P.cyclicDart_seam Q.cyclicDart_seam P.length Q.length P.cyclicDart_period Q.cyclicDart_period
    (fun i _ => P.cyclicDart_next_edge_ne i) (fun j _ => Q.cyclicDart_next_edge_ne j)

end Paper170Geometry.TruncatedSpokeCoordinates

end
end

section

/-! Reconstruction of the frozen cycle pairing from faithful local coordinates. -/
noncomputable section
namespace Paper170
open Paper170Geometry
variable {Vertex Edge : Type} [Fintype Vertex] [Fintype Edge]
  {graph : Graph Vertex Edge}

theorem cycle_pairing_of_coordinates (N : NormalizedDrawing graph) (O : SpokeOrders N)
    (V : VertexTruncation N.toContinuousDrawing) (C : TruncatedSpokeCoordinates V)
    (hnode : ∀v (e f : IncidentEdges graph v),
      Zarankiewicz.orderSign (C.node v e) (C.node v f) = spokeComparison O v e.val f.val)
    (z z' : Edge → ℝ) (hz : ∀v, boundary graph z v = 0) (hz' : ∀v, boundary graph z' v = 0) :
    edgePairing (cycleIntersection O) z z' = 0 := by
  have hmatrix : C.cycleIntersectionMatrix = cycleIntersection O := by
    funext e f
    unfold TruncatedSpokeCoordinates.cycleIntersectionMatrix cycleIntersection
    rw [VertexTruncation.signedIntersection_eq_interiorIntersection N V,
      C.edgeEndpointPairing_eq_signed_sum O hnode]
  rw [← hmatrix]
  exact C.cycleMatrix_pairing_zero (normalized_noAdjacent N) (normalized_locallyStraight N)
    (normalized_locallyTransverse N) z z' hz hz'

end Paper170

end
end

section

/-! The source cycle identity for every normalized ordinary drawing. -/
noncomputable section
namespace Paper170
open Paper170Geometry

theorem cycle_pairing {Vertex Edge : Type} [Fintype Vertex] [Fintype Edge]
    (G : Graph Vertex Edge) (N : NormalizedDrawing G) (O : SpokeOrders N)
    (z z' : Edge → ℝ) (hz : ∀v, boundary G z v = 0) (hz' : ∀v, boundary G z' v = 0) :
    edgePairing (cycleIntersection O) z z' = 0 := by
  obtain ⟨V⟩ := normalized_vertexTruncation N
  obtain ⟨C,hC⟩ := exists_truncatedSpokeCoordinates_compatible N V O
  exact cycle_pairing_of_coordinates N O V C hC z z' hz hz'

theorem raw_cycle_pairing {n : ℕ} (N : NormalizedDrawing (completeGraph n)) (O : SpokeOrders N)
    (z z' : Fin n → Fin n → ℝ) (hz : ∀v, chainBoundary z v = 0) (hz' : ∀v, chainBoundary z' v = 0) :
    chainPairing (rawCycleIntersection O) z z' = 0 := by
  rw [chainPairing_rawCycleIntersection]
  apply cycle_pairing (completeGraph n) N O (liftedChain z) (liftedChain z')
  · simpa only [boundary_liftedChain] using hz
  · simpa only [boundary_liftedChain] using hz'

end Paper170

end
end

end OAI
