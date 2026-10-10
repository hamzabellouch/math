import OAI.Combinatorics.Crossing.EndpointFlagPairing
import OAI.Combinatorics.Crossing.CyclicSumArithmetic
import OAI.Combinatorics.Crossing.RectangleAlgebra

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
open scoped BigOperators
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem passage_sum_eq_endpoint_sum (d f : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
    (N K : ℕ) (hN : d N=d 0) (hK : f K=f 0) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K, C.passagePairing d f hd hf i j)=
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
        bipartiteDartSign (d i)*bipartiteDartSign (f j)*
          C.edgeEndpointPairing (bipartiteDartEdge (d i)) (bipartiteDartEdge (f j)) := by
  have hTS := double_sum_cycle_shift_right d f N K hK
    (fun a b => C.flagPairing (dartTargetFlag a) (dartSourceFlag b))
  have hST := double_sum_cycle_shift_left d f N K hN
    (fun a b => C.flagPairing (dartSourceFlag a) (dartTargetFlag b))
  have hSS₀ := double_sum_cycle_shift_right (fun i => d (i+1)) f N K hK
    (fun a b => C.flagPairing (dartSourceFlag a) (dartSourceFlag b))
  have hSS₁ := double_sum_cycle_shift_left d f N K hN
    (fun a b => C.flagPairing (dartSourceFlag a) (dartSourceFlag b))
  simp_rw [C.passagePairing_flags,← C.dart_endpoint_pairing]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [hTS,hST,hSS₀,hSS₁]

def cycleIntersectionMatrix : Matrix (BipartiteEdge m n) (BipartiteEdge m n) ℝ :=
  fun e f => V.signedIntersection e f+C.edgeEndpointPairing e f

theorem closed_cycle_matrix_sum (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (d f : ℕ → (completeBipartite m n).Dart)
    (hd : ∀ i, (d i).snd=(d (i+1)).fst) (hf : ∀ j, (f j).snd=(f (j+1)).fst)
    (N K : ℕ) (hN : d N=d 0) (hK : f K=f 0)
    (hdi : ∀ i, i < N → bipartiteDartEdge (d (i+1)) ≠ bipartiteDartEdge (d i))
    (hfj : ∀ j, j < K → bipartiteDartEdge (f (j+1)) ≠ bipartiteDartEdge (f j)) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range K,
      bipartiteDartSign (d i)*bipartiteDartSign (f j)*
        C.cycleIntersectionMatrix (bipartiteDartEdge (d i)) (bipartiteDartEdge (f j))=0 := by
  have hh := C.closed_cycle_averaged_sum hnorm hstraight htrans d f hd hf N K hN hK hdi hfj
  simp only [Finset.sum_add_distrib] at hh
  rw [C.passage_sum_eq_endpoint_sum d f hd hf N K hN hK] at hh
  simpa only [cycleIntersectionMatrix,mul_add,Finset.sum_add_distrib] using hh

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
