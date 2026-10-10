import OAI.NumberTheory.Ostmann.MainWithoutPage
import OAI.NumberTheory.Ostmann.ZeroDensity.ActualProgressionInput

namespace OAI

/-! # Main statements with all exceptional-zero data constructed -/

namespace Ostmann

theorem twoInfiniteSummandsImpossible_of_actual_progression
    (hP : ActualProgressionTheta) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    TwoInfiniteSummandsImpossible :=
  twoInfiniteSummandsImpossible_without_real_zero_input
    (progressionInput_of_actual_theta hP) ls hsize hSiegel sieve hD actualComplexZeroRegion

theorem inverseGoldbach_of_actual_progression
    (hP : ActualProgressionTheta) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    InverseGoldbach :=
  inverseGoldbach_without_real_zero_input
    (progressionInput_of_actual_theta hP) ls hsize hSiegel sieve hD actualComplexZeroRegion

end Ostmann

end OAI
