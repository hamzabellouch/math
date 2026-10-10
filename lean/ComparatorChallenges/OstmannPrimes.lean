import Mathlib

namespace OAI

open scoped Pointwise symmDiff

namespace Ostmann

theorem main : ∀ A B : Set ℕ, A.Nontrivial → B.Nontrivial →
    Set.Infinite ((A + B) ∆ {n : ℕ | Nat.Prime n}) := by
  sorry

end Ostmann

end OAI
