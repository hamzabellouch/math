import OAI.NumberTheory.Ostmann.Statement

namespace OAI

open scoped Pointwise symmDiff

namespace Ostmann

structure Decomposition where
  A : Set ℕ
  B : Set ℕ
  infinite_A : A.Infinite
  infinite_B : B.Infinite
  cutoff : ℕ
  prime_iff : ∀ n, cutoff ≤ n → (n ∈ A + B ↔ Nat.Prime n)

namespace Decomposition

theorem eventuallyEqual (d : Decomposition) :
    EventuallyEqual (d.A + d.B) primes := by
  refine ⟨d.cutoff, ?_⟩
  intro n hn
  exact d.prime_iff n hn

theorem sum_prime (d : Decomposition) {a b : ℕ}
    (ha : a ∈ d.A) (hb : b ∈ d.B) (h : d.cutoff ≤ a + b) :
    Nat.Prime (a + b) :=
  (d.prime_iff (a + b) h).mp (Set.add_mem_add ha hb)

theorem prime_covered (d : Decomposition) {p : ℕ}
    (hp : Nat.Prime p) (h : d.cutoff ≤ p) :
    ∃ a ∈ d.A, ∃ b ∈ d.B, a + b = p := by
  exact (d.prime_iff p h).mpr hp

end Decomposition
end Ostmann

end OAI
