import OAI.Analysis.MarkovType.FiniteWalkCoordinates
import OAI.Analysis.MarkovType.FiniteWalkMoment
import OAI.Analysis.MarkovType.MarkedMoments
import OAI.Analysis.MarkovType.OrderedMarkovTransfer

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem FiniteWalkWitness.markov_moment_bound {N : OrderedNorm} {n : ℕ}
    (W : FiniteWalkWitness N n) (hn : 1 ≤ n) {p K : ℝ}
    (hX : MarkovTypeWith p K X) (hNX : CoordinatesRepresentable X N) :
    (3 / 20 : ℝ) * ((n : ℝ) / 24) ^ p ≤ K ^ p * (n : ℝ) := by
  let : Fintype W.State := W.stateFintype
  let : Fintype W.Edge := W.edgeFintype
  have hupper := hX.odd_edge_bound_coordinates N hNX W.coordinateBound
    W.chain W.coordinateLabel W.coordinateLabel_odd n hn
  rw [stationaryEdgeCost_eq_one W.chain W.coordinateLabel p W.coordinateLabel_norm,
    mul_one, W.coordinateLabel_markedSumCost p n] at hupper
  exact (W.moment_lower hX.1.le).trans hupper

end MarkovSuperreflexivity

end

end OAI
