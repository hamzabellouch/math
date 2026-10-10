import OAI.NumberTheory.Ostmann.Complete

namespace OAI

/-! # Main statements of The additive indecomposability of the primes -/

namespace OstmannPaper

open scoped symmDiff

/-- Theorem 1.1, including every finite modification of the primes. -/
theorem inverse_goldbach (A B : Set ℕ) (hA : A.Nontrivial) (hB : B.Nontrivial) :
    (Ostmann.sumset A B ∆ Ostmann.primes).Infinite :=
  Ostmann.inverseGoldbach A B hA hB

/-- Theorem 2.3, the two-infinite-summand formulation. -/
theorem two_infinite_summands (A B : Set ℕ) (hA : A.Infinite) (hB : B.Infinite) :
    ¬ (Ostmann.sumset A B ∆ Ostmann.primes).Finite := by
  intro hfinite
  exact Ostmann.twoInfiniteSummandsImpossible A B hA hB
    ((Ostmann.finite_symmDiff_iff A B).mp hfinite)

end OstmannPaper

end OAI
