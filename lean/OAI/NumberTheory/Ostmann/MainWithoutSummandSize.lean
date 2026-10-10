import OAI.NumberTheory.Ostmann.MainWithoutAdditiveSieve
import OAI.NumberTheory.Ostmann.Preliminaries.SummandSizeProof

namespace OAI

/-! # Both main theorems after proving the required summand-size bounds -/

namespace Ostmann

theorem twoInfiniteSummandsImpossible_without_summand_size
    (hSiegel : PublishedSiegelBound) (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    TwoInfiniteSummandsImpossible :=
  twoInfiniteSummandsImpossible_without_additive_sieve
    publishedSummandSizeBound hSiegel sieve hD

theorem inverseGoldbach_without_summand_size
    (hSiegel : PublishedSiegelBound) (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    InverseGoldbach :=
  inverseGoldbach_without_additive_sieve publishedSummandSizeBound hSiegel sieve hD

end Ostmann

end OAI
