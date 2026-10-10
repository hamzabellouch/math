import OAI.Analysis.MarkovType.FiniteWalkWitness
import OAI.Analysis.MarkovType.OrderedCoordinates
import OAI.Analysis.MarkovType.NormCompression

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

attribute [local instance] FiniteWalkWitness.stateFintype FiniteWalkWitness.edgeFintype

namespace FiniteWalkWitness

variable {N : OrderedNorm} {n : ℕ}

def coordinateLabel (W : FiniteWalkWitness N n) (e : W.Edge) :
    CoordinateSpace N W.coordinateBound :=
  fun i => W.label e i.val

theorem coordinateLabel_reconstruct (W : FiniteWalkWitness N n) (e : W.Edge) :
    C00.ofArray (W.coordinateLabel e) = W.label e := by
  exact C00.ofArray_restrict (W.label e) W.coordinateBound (W.support_bound e)

theorem coordinateLabel_odd (W : FiniteWalkWitness N n) :
    OddLabel W.chain W.coordinateLabel := by
  intro e
  funext i
  exact congrArg (fun x : C00 => x i.val) (W.odd e)

theorem coordinateLabel_norm (W : FiniteWalkWitness N n) (e : W.Edge) :
    ‖W.coordinateLabel e‖ = 1 := by
  rw [CoordinateSpace.norm_eq, W.coordinateLabel_reconstruct]
  exact W.unit e

theorem coordinateLabel_edgeSum_reconstruct (W : FiniteWalkWitness N n) {k : ℕ}
    (ω : MarkedPath W.State W.Edge k) :
    C00.ofArray (edgeSum W.coordinateLabel ω) = edgeSum W.label ω := by
  change (C00.arrayLinear W.coordinateBound)
      (∑ i : Fin k, W.coordinateLabel (ω.2 i)) = ∑ i : Fin k, W.label (ω.2 i)
  refine (map_sum (C00.arrayLinear W.coordinateBound)
    (fun i : Fin k => W.coordinateLabel (ω.2 i)) Finset.univ).trans ?_
  apply Finset.sum_congr rfl
  intro i _
  exact W.coordinateLabel_reconstruct (ω.2 i)

theorem coordinateLabel_edgeSum_norm (W : FiniteWalkWitness N n) {k : ℕ}
    (ω : MarkedPath W.State W.Edge k) :
    ‖edgeSum W.coordinateLabel ω‖ = N (edgeSum W.label ω) := by
  change N (C00.ofArray (edgeSum W.coordinateLabel ω)) = _
  exact congrArg N (W.coordinateLabel_edgeSum_reconstruct ω)

theorem coordinateLabel_escape (W : FiniteWalkWitness N n) :
    (3 : ℝ) / 20 ≤ markedProb W.chain n
      (fun ω => (n : ℝ) / 24 ≤ ‖edgeSum W.coordinateLabel ω‖) := by
  simpa only [W.coordinateLabel_edgeSum_norm] using W.escape

theorem coordinateLabel_markedSumCost (W : FiniteWalkWitness N n) (p : ℝ) (k : ℕ) :
    markedSumCost W.chain W.coordinateLabel p k =
      markedExpect W.chain k (fun ω => Real.rpow (N (edgeSum W.label ω)) p) := by
  simp only [markedSumCost, W.coordinateLabel_edgeSum_norm]

end FiniteWalkWitness

end MarkovSuperreflexivity

end

end OAI
