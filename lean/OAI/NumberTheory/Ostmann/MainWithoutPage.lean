import OAI.NumberTheory.Ostmann.Preliminaries.ReducedPublishedInputs
import OAI.NumberTheory.Ostmann.ZeroDensity.ProgressionWithoutPage
import OAI.NumberTheory.Ostmann.ZeroDensity.ActualComplexZeroRegion

namespace OAI

/-! # Exact main statements after discharging the Page and zero-region inputs -/

namespace Ostmann

theorem twoInfiniteSummandsImpossible_without_page_input
    (P : PublishedProgressionEstimate) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    TwoInfiniteSummandsImpossible :=
  twoInfiniteSummandsImpossible_without_real_zero_input P.toPublished ls hsize hSiegel
    sieve hD actualComplexZeroRegion

theorem inverseGoldbach_without_page_input
    (P : PublishedProgressionEstimate) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    InverseGoldbach :=
  inverseGoldbach_without_real_zero_input P.toPublished ls hsize hSiegel
    sieve hD actualComplexZeroRegion

end Ostmann

end OAI
