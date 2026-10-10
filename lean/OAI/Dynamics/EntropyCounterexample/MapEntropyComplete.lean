import OAI.Dynamics.EntropyCounterexample.MapEntropy
import OAI.Dynamics.EntropyCounterexample.MapOrbitAlternatives

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem coverEntropy_realizedMap_eq_zero (L : ℝ) (hL : 2 < L) :
    Dynamics.coverEntropy (realizedMap L hL)
      (Set.univ : Set (CounterexampleManifold 3)) = (0 : EReal) :=
  coverEntropy_realizedMap_eq_zero_of_orbit_alternatives L hL
    (concrete_orbit_alternatives L hL)

end Problem340.Construction

end

end OAI
