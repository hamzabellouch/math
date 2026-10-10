import Mathlib.NumberTheory.Chebyshev
import OAI.NumberTheory.Ostmann.Preliminaries.TailStability

namespace OAI

namespace Ostmann

open scoped BigOperators

/-- The precise one-sided consequence of Mertens' first theorem needed by
the collision argument. `C` is fixed independently of the cutoff. -/
def MertensLowerBound (C : ℝ) : Prop :=
  ∀ Q : ℕ, 1 ≤ Q → Real.log (Q : ℝ) - C ≤
    ∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / (p : ℝ)

theorem prime_log_weight_le (Q : ℕ) :
    (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) ≤ Real.log 4 * Q := by
  rw [← Chebyshev.theta_eq_sum_primesLE_log]
  exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg Q)

/-- Collision stability on all primes up to `Q`, conditional on exactly the
lower prime-sum estimate above. This is a component of the main proof, not
the paper's infinite-summand theorem. -/
theorem EventuallyPrimeSumset.tail_collision_stability_of_mertens
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    {C : ℝ} (hM : MertensLowerBound C) :
    ∃ N, ∀ (A₀ B₀ : Finset ℕ) (μ ν : ℕ → ℝ) (X Q : ℕ) (m : ℝ),
      1 ≤ X → 1 ≤ Q →
      (∀ a ∈ A₀, a ∈ A ∧ N + Q < a ∧ a ≤ X) →
      (∀ b ∈ B₀, b ∈ B ∧ N + Q < b ∧ b ≤ X) →
      (∀ a ∈ A₀, 0 ≤ μ a) → (∀ b ∈ B₀, 0 ≤ ν b) →
      (∑ a ∈ A₀, μ a) = 1 → (∑ b ∈ B₀, ν b) = 1 →
      (∀ a ∈ A₀, μ a ≤ m) → (∀ b ∈ B₀, ν b ≤ m) → 0 ≤ m →
      0 ≤ (∑ p ∈ Nat.primesLE Q,
        Real.log (p : ℝ) * tailCollisionDefect A N p A₀ B₀ μ ν) ∧
      (∑ p ∈ Nat.primesLE Q,
        Real.log (p : ℝ) * tailCollisionDefect A N p A₀ B₀ μ ν) ≤
        2 * Real.log (X : ℝ) - 4 * Real.log (Q : ℝ) + 4 * C +
          2 * m * Real.log 4 * Q := by
  obtain ⟨N, hN⟩ := h.tail_collision_stability hA hB
  refine ⟨N, ?_⟩
  intro A₀ B₀ μ ν X Q m hX hQ hAtail hBtail hμ hν hmassμ hmassν hatomμ hatomν hm
  exact hN (Nat.primesLE Q) A₀ B₀ μ ν X Q m (Real.log 4) C hX
    (fun p hp => ⟨Nat.prime_of_mem_primesLE hp, Nat.le_of_mem_primesLE hp⟩)
    hAtail hBtail hμ hν hmassμ hmassν hatomμ hatomν hm
    (prime_log_weight_le Q) (hM Q hQ)

end Ostmann

end OAI
