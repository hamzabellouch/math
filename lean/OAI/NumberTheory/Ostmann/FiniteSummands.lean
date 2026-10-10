import OAI.NumberTheory.Ostmann.Basic
import OAI.NumberTheory.Ostmann.FiniteFactor

namespace OAI

/-! The finite-summand reduction follows from Dirichlet's theorem and the Chinese remainder theorem. -/

namespace Ostmann

/-- A finite nontrivial summand is incompatible with eventual equality to the
primes. The only analytic input is Dirichlet's theorem for one reduced residue
class, provided by `Nat.forall_exists_prime_gt_and_modEq`. -/
theorem not_eventuallyPrimeSumset_of_finite_left {A B : Set ℕ}
    (hA : A.Nontrivial) (hfin : A.Finite) : ¬ EventuallyPrimeSumset A B := by
  intro h
  exact finite_factor_impossible A B hfin hA h

/-- The finite-summand reduction is symmetric. -/
theorem not_eventuallyPrimeSumset_of_finite_right {A B : Set ℕ}
    (hB : B.Nontrivial) (hfin : B.Finite) : ¬ EventuallyPrimeSumset A B := by
  intro h
  exact not_eventuallyPrimeSumset_of_finite_left hB hfin h.symm

/-- Lemma 2.2: both summands of an eventual decomposition are infinite. -/
theorem infinite_summands {A B : Set ℕ} (hA : A.Nontrivial) (hB : B.Nontrivial)
    (h : EventuallyPrimeSumset A B) : A.Infinite ∧ B.Infinite := by
  constructor
  · exact fun hfin => not_eventuallyPrimeSumset_of_finite_left hA hfin h
  · exact fun hfin => not_eventuallyPrimeSumset_of_finite_right hB hfin h

end Ostmann

end OAI
