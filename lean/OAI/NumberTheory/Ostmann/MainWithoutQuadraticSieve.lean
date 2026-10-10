import OAI.NumberTheory.Ostmann.MainWithoutSiegel
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveProof

namespace OAI

/-! # Both main theorems after proving the quadratic large sieve -/

namespace Ostmann

theorem twoInfiniteSummandsImpossible_without_quadratic_sieve
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    TwoInfiniteSummandsImpossible :=
  twoInfiniteSummandsImpossible_without_siegel publishedQuadraticLargeSieve hD

theorem inverseGoldbach_without_quadratic_sieve
    (hD : PublishedComplexZeroDensity actualCharacterZeros) : InverseGoldbach :=
  inverseGoldbach_without_siegel publishedQuadraticLargeSieve hD

end Ostmann

end OAI
