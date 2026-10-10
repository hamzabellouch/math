import OAI.NumberTheory.Ostmann.MainWithoutQuadraticSieve
import OAI.NumberTheory.Ostmann.ZeroDensity.ComplexDensityProof

namespace OAI

/-! # Ostmann's inverse Goldbach theorems

The quadratic large sieve and the exact character-zero density estimate give
both the two-infinite-summands contradiction and asymptotic indecomposability.
-/

namespace Ostmann

/-- Theorem 2.3: two infinite nonnegative summands cannot give the primes
outside a finite initial interval. -/
theorem twoInfiniteSummandsImpossible : TwoInfiniteSummandsImpossible :=
  twoInfiniteSummandsImpossible_without_quadratic_sieve publishedComplexZeroDensity

/-- Theorem 1.1: every sum of two nontrivial sets of nonnegative integers has
infinite symmetric difference with the primes. -/
theorem inverseGoldbach : InverseGoldbach :=
  inverseGoldbach_without_quadratic_sieve publishedComplexZeroDensity

end Ostmann

end OAI
