import OAI.NumberTheory.SiegelZeros.Estimates.GeometricBoundary

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.W50

open WeightedTorusJets

theorem uniform_exclusion_of_local_isolated_bezout
    (hBezout : W22.LocalIsolatedBezoutStatement ℂ) :
    UniformSiegelZeroExclusion := by
  apply uniform_exclusion_of_actual_cutoff
  intro H N hH hHN _hN d a hd hd1 hd2 ha
  exact W28.actualCutoffSpanning_of_localBezout hBezout H N (by omega) hHN
    d hd hd1 hd2 a ha

end SiegelZerosAwei.W50

end

end SiegelZeros

end OAI
