import Mathlib

namespace OAI

open scoped Pointwise symmDiff

namespace Ostmann

def primes : Set ℕ := {n | Nat.Prime n}

abbrev sumset (A B : Set ℕ) : Set ℕ := A + B

def EventuallyPrimeSumset (A B : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n → (n ∈ sumset A B ↔ n.Prime)

def TwoInfiniteSummandsImpossible : Prop :=
  ∀ A B : Set ℕ, A.Infinite → B.Infinite → ¬ EventuallyPrimeSumset A B

def InverseGoldbach : Prop :=
  ∀ A B : Set ℕ, A.Nontrivial → B.Nontrivial →
    Set.Infinite (@symmDiff (Set ℕ)
      (@SemilatticeSup.toMax (Set ℕ)
        (@Lattice.toSemilatticeSup (Set ℕ)
          (@CompleteLattice.toLattice (Set ℕ)
            (@CompleteBooleanAlgebra.toCompleteLattice (Set ℕ)
              (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra (Set ℕ)
                (@Set.instCompleteAtomicBooleanAlgebra ℕ))))))
      Set.instSDiff (sumset A B) primes)

theorem inverseGoldbach : InverseGoldbach := by
  sorry

theorem twoInfiniteSummandsImpossible : TwoInfiniteSummandsImpossible := by
  sorry

end Ostmann

end OAI
