import OAI.NumberTheory.Ostmann.MainWithoutSummandSize
import OAI.NumberTheory.Ostmann.ZeroDensity.SiegelBoundProof

namespace OAI

/-! # Both main theorems after proving the actual Siegel zero bound -/

namespace Ostmann

theorem twoInfiniteSummandsImpossible_without_siegel
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    TwoInfiniteSummandsImpossible :=
  twoInfiniteSummandsImpossible_without_summand_size publishedSiegelBound sieve hD

theorem inverseGoldbach_without_siegel
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    InverseGoldbach :=
  inverseGoldbach_without_summand_size publishedSiegelBound sieve hD

end Ostmann

end OAI
