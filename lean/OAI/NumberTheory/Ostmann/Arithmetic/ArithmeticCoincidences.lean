import OAI.NumberTheory.Ostmann.Arithmetic.WeightedPolynomialRoots
import OAI.NumberTheory.Ostmann.Preliminaries.PrimeDivisors

namespace OAI

/-! # Accidental prime congruences in the arithmetic comparison

These finite estimates implement the two errors in §8: an exact polynomial
zero, and an independent sampled prime dividing a nonzero evaluation.
-/

namespace Ostmann

open scoped BigOperators

/-- A lower bound on the sizes of the sampled primes converts the logarithmic
prime-divisor budget into a bound on their number. -/
theorem prime_divisor_card_le (P : Finset ℕ) {n : ℕ} (hn : 0 < n)
    (hprime : ∀ p ∈ P, p.Prime) (B K : ℝ) (hB : 0 < B)
    (hsize : ∀ p ∈ P, B ≤ Real.log (p : ℝ))
    (hlog : Real.log (n : ℝ) ≤ K * B) :
    ((P.filter fun p => p ∣ n).card : ℝ) ≤ K := by
  classical
  have hsum := sum_log_prime_divisors_le (P.filter fun p => p ∣ n) hn
    (fun p hp => hprime p (Finset.mem_filter.mp hp).1)
    (fun _ hp => (Finset.mem_filter.mp hp).2)
  have hlower : ((P.filter fun p => p ∣ n).card : ℝ) * B ≤
      ∑ p ∈ P.filter (fun p => p ∣ n), Real.log (p : ℝ) := by
    calc
      _ = ∑ _p ∈ P.filter (fun p => p ∣ n), B := by simp
      _ ≤ _ := Finset.sum_le_sum fun p hp => hsize p (Finset.mem_filter.mp hp).1
  exact (mul_le_mul_iff_left₀ hB).mp (hlower.trans (hsum.trans hlog))

/-- The probability of an independent prime dividing a nonzero integer is
bounded by its maximal atom times the number of possible prime divisors. -/
theorem prime_divisibility_prior_le (P : Finset ℕ) (ν : ℕ → ℝ)
    (β K : ℝ) (hβ : 0 ≤ β) (hν : ∀ p ∈ P, ν p ≤ β)
    (n : ℕ) (hcard : ((P.filter fun p => p ∣ n).card : ℝ) ≤ K) :
    (∑ p ∈ P, if p ∣ n then ν p else 0) ≤ K * β := by
  classical
  calc
    _ = ∑ p ∈ P.filter (fun p => p ∣ n), ν p := (Finset.sum_filter _ _).symm
    _ ≤ ∑ _p ∈ P.filter (fun p => p ∣ n), β :=
      Finset.sum_le_sum fun p hp => hν p (Finset.mem_filter.mp hp).1
    _ = ((P.filter fun p => p ∣ n).card : ℝ) * β := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hβ

/-- Separate the exact-zero event from the independent prime-divisor event.
No conditional equidistribution is used in this estimate. -/
theorem accidental_divisibility_le {X : Type*} [Fintype X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hmass : ∑ x, w x = 1)
    (P : Finset ℕ) (ν : ℕ → ℝ) (hνmass : ∑ p ∈ P, ν p = 1)
    (N : X → ℕ) (β K : ℝ) (hβ : 0 ≤ β) (hK : 0 ≤ K)
    (hν : ∀ p ∈ P, ν p ≤ β)
    (hcard : ∀ x, N x ≠ 0 → ((P.filter fun p => p ∣ N x).card : ℝ) ≤ K) :
    (∑ x, w x * ∑ p ∈ P, if p ∣ N x then ν p else 0) ≤
      (∑ x, w x * if N x = 0 then 1 else 0) + K * β := by
  classical
  have hpoint (x : X) : (∑ p ∈ P, if p ∣ N x then ν p else 0) ≤
      (if N x = 0 then 1 else 0) + K * β := by
    by_cases hx : N x = 0
    · simp only [hx, dvd_zero, ite_true, hνmass]
      exact le_add_of_nonneg_right (mul_nonneg hK hβ)
    · simp only [hx, ite_false, zero_add]
      exact prime_divisibility_prior_le P ν β K hβ hν (N x) (hcard x hx)
  calc
    _ ≤ ∑ x, w x * ((if N x = 0 then 1 else 0) + K * β) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (hw x)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hmass, one_mul]

/-- The arithmetic coincidence bound with the exact-zero probability supplied
by the proved weighted polynomial root estimate. -/
theorem polynomial_prime_coincidence_le {A : Type*} [Fintype A] {n : ℕ}
    (value : A → ℚ) (hinj : Function.Injective value)
    (F : MvPolynomial (Fin n) ℚ) (hF : F ≠ 0)
    (μ : Fin n → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1)
    (α : ℝ) (hα : 0 ≤ α) (hmax : ∀ i a, μ i a ≤ α)
    (P : Finset ℕ) (ν : ℕ → ℝ) (hνmass : ∑ p ∈ P, ν p = 1)
    (N : (Fin n → A) → ℕ)
    (hzero : ∀ x, N x = 0 ↔ MvPolynomial.eval (fun i => value (x i)) F = 0)
    (β K : ℝ) (hβ : 0 ≤ β) (hK : 0 ≤ K) (hν : ∀ p ∈ P, ν p ≤ β)
    (hcard : ∀ x, N x ≠ 0 → ((P.filter fun p => p ∣ N x).card : ℝ) ≤ K) :
    (∑ x, productPrior μ x * ∑ p ∈ P, if p ∣ N x then ν p else 0) ≤
      (F.totalDegree : ℝ) * α + K * β := by
  classical
  refine (accidental_divisibility_le (productPrior μ) (productPrior_nonneg μ hμ)
    (productPrior_mass μ hmass) P ν hνmass N β K hβ hK hν hcard).trans ?_
  refine add_le_add ?_ le_rfl
  simp_rw [hzero]
  exact weighted_polynomial_roots_le value hinj α hα F hF μ hμ hmass hmax

end Ostmann

end OAI
