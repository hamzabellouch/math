import OAI.NumberTheory.Ostmann.MainWithoutProgression
import OAI.NumberTheory.Ostmann.Preliminaries.AdditiveSieveProof

namespace OAI

/-! # Both main theorems after discharging the additive large sieve -/

namespace Ostmann

theorem twoInfiniteSummandsImpossible_without_additive_sieve
    (hsize : PublishedSummandSizeBound) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    TwoInfiniteSummandsImpossible :=
  twoInfiniteSummandsImpossible_without_progression_input
    publishedAdditiveLargeSieve hsize hSiegel sieve hD

theorem inverseGoldbach_without_additive_sieve
    (hsize : PublishedSummandSizeBound) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    InverseGoldbach :=
  inverseGoldbach_without_progression_input publishedAdditiveLargeSieve hsize hSiegel sieve hD

end Ostmann

end OAI
