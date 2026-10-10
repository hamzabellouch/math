import OAI.NumberTheory.Ostmann.MainActualProgression
import OAI.NumberTheory.Ostmann.ZeroDensity.ActualThetaEstimate

namespace OAI

/-! # The main statements after discharging the prime-progression input -/

namespace Ostmann

noncomputable def actualProgressionInput : PublishedProgressionInput :=
  progressionInput_of_actual_theta actualProgressionTheta

theorem twoInfiniteSummandsImpossible_without_progression_input
    (ls : PublishedAdditiveLargeSieve) (hsize : PublishedSummandSizeBound)
    (hSiegel : PublishedSiegelBound) (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    TwoInfiniteSummandsImpossible :=
  twoInfiniteSummandsImpossible_of_actual_progression
    actualProgressionTheta ls hsize hSiegel sieve hD

theorem inverseGoldbach_without_progression_input
    (ls : PublishedAdditiveLargeSieve) (hsize : PublishedSummandSizeBound)
    (hSiegel : PublishedSiegelBound) (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    InverseGoldbach :=
  inverseGoldbach_of_actual_progression actualProgressionTheta ls hsize hSiegel sieve hD

end Ostmann

end OAI
