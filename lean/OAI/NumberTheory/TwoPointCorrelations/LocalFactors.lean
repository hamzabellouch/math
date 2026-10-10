import OAI.NumberTheory.TwoPointCorrelations.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace OAI

/-!
# Multiplicative functions from local prime-power factors

The finite local expansions in Part III of the manuscript replace values at
primes dividing a fixed dilation. The resulting functions are ordinary
multiplicative functions; complete multiplicativity is not required.
-/

namespace TwoPointCorrelations

/-- Multiply local factors over the positive exponents in the prime factorization. -/
noncomputable def fromPrimePowers (F : ℕ → ℕ → ℂ) (n : ℕ) : ℂ :=
  n.factorization.prod F

@[simp] theorem fromPrimePowers_one (F : ℕ → ℕ → ℂ) : fromPrimePowers F 1 = 1 := by
  simp [fromPrimePowers]

/-- Coprime arguments have disjoint prime support, so arbitrary prime-power
values give an ordinary multiplicative function. -/
theorem fromPrimePowers_multiplicative (F : ℕ → ℕ → ℂ) :
    Multiplicative (fromPrimePowers F) := by
  intro m n hm hn hcop
  unfold fromPrimePowers
  rw [Nat.factorization_mul hm.ne' hn.ne']
  apply Finsupp.prod_add_index_of_disjoint
  simpa only [Nat.support_factorization] using hcop.disjoint_primeFactors

theorem fromPrimePowers_oneBounded (F : ℕ → ℕ → ℂ)
    (hF : ∀ p k, Nat.Prime p → 0 < k → ‖F p k‖ ≤ 1) :
    OneBounded (fromPrimePowers F) := by
  intro n hn
  unfold fromPrimePowers Finsupp.prod
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro p hp
    exact norm_nonneg _
  · intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
    have hk : 0 < n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    exact hF p _ hprime hk

@[simp] theorem fromPrimePowers_prime (F : ℕ → ℕ → ℂ) {p : ℕ} (hp : Nat.Prime p) :
    fromPrimePowers F p = F p 1 := by
  simp [fromPrimePowers, hp.factorization, Finsupp.prod]

/-- A change at finitely many prime-power sequences changes only those prime values. -/
theorem fromPrimePowers_eq_at_prime (F G : ℕ → ℕ → ℂ) (P : Finset ℕ)
    (hFG : ∀ p, p ∉ P → F p 1 = G p 1) {p : ℕ} (hp : Nat.Prime p) (hpP : p ∉ P) :
    fromPrimePowers F p = fromPrimePowers G p := by
  simp only [fromPrimePowers_prime F hp, fromPrimePowers_prime G hp]
  exact hFG p hpP

/-- The local construction recovers a normalized multiplicative function on
positive integers, without replacing its prime-power values by powers. -/
theorem fromPrimePowers_reconstruct (f : ℕ → ℂ) (hf : Multiplicative f)
    (h1 : f 1 = 1) {n : ℕ} (hn : 0 < n) :
    fromPrimePowers (fun p k => f (p ^ k)) n = f n := by
  symm
  apply Nat.multiplicative_factorization f _ h1 hn.ne'
  intro a b hab
  by_cases ha : a = 0
  · subst a
    have hb : b = 1 := by simpa using hab
    subst b
    simp [h1]
  by_cases hb : b = 0
  · subst b
    have ha : a = 1 := by simpa using hab
    subst a
    simp [h1]
  exact hf a b (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) hab

end TwoPointCorrelations

end OAI
