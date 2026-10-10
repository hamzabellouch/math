import OAI.Analysis.MarkovType.OddEdgeTransfer
import OAI.Analysis.MarkovType.OrderedCoordinates

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {p K : ℝ}

theorem MarkovTypeWith.coordinateSpace (hX : MarkovTypeWith p K X)
    (N : OrderedNorm) (hNX : CoordinatesRepresentable X N) (m : ℕ) :
    MarkovTypeWith p K (CoordinateSpace N m) :=
  hX.of_near_isometric_embeddings ((coordinatesRepresentable_iff N).mp hNX m)

theorem MarkovTypeWith.odd_edge_bound_coordinates
    {S E : Type*} [Fintype S] [Fintype E]
    (hX : MarkovTypeWith p K X) (N : OrderedNorm)
    (hNX : CoordinatesRepresentable X N) (m : ℕ)
    (C : FiniteMarkedChain S E) (g : E → CoordinateSpace N m)
    (hg : OddLabel C g) (n : ℕ) (hn : 1 ≤ n) :
    markedSumCost C g p n ≤ Real.rpow K p * (n : ℝ) * stationaryEdgeCost C g p :=
  (hX.coordinateSpace N hNX m).odd_edge_bound C g hg n hn

end MarkovSuperreflexivity

end

end OAI
