import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCoprimeBound

namespace OAI

/-! # Exact Euler cancellation of the two quadratic Poisson main terms

This is the finite arithmetic identity in Heath-Brown (1995), §7, Lemma 5.
The monomial index records the integer in each character, not a formal degree.
-/

namespace Ostmann

open scoped Classical BigOperators
open MonoidAlgebra

private noncomputable def quadraticMonomial (k : ℕ) : ArithmeticFunction (MonoidAlgebra ℤ ℕ) :=
  ⟨fun n => if n = 0 then 0 else single (n ^ k) 1, by simp⟩

private theorem quadraticMonomial_multiplicative (k : ℕ) :
    (quadraticMonomial k).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [quadraticMonomial, MonoidAlgebra.one_def]
  · intro a b ha hb _
    simp [quadraticMonomial, ha, hb, mul_ne_zero ha hb, mul_pow]

private theorem quadraticMonomial_euler_add {n : ℕ} (hn : Squarefree n) (k : ℕ) :
    (∏ p ∈ n.primeFactors, (1 + single (p ^ k) (1 : ℤ))) =
      ∑ d ∈ n.divisors, single (d ^ k) (1 : ℤ) := by
  have hh := (quadraticMonomial_multiplicative k).prodPrimeFactors_one_add_of_squarefree hn
  calc
    _ = ∏ p ∈ n.primeFactors, (1 + quadraticMonomial k p) := by
      apply Finset.prod_congr rfl
      intro p hp
      simp [quadraticMonomial, (Nat.prime_of_mem_primeFactors hp).ne_zero]
    _ = _ := hh
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [quadraticMonomial, (Nat.pos_of_mem_divisors hd).ne']

private theorem quadraticMonomial_euler_sub {n : ℕ} (hn : Squarefree n) (k : ℕ) :
    (∏ p ∈ n.primeFactors, (1 - single (p ^ k) (1 : ℤ))) =
      ∑ d ∈ n.divisors, single (d ^ k) (ArithmeticFunction.moebius d) := by
  have hh := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    (quadraticMonomial k) (quadraticMonomial_multiplicative k) hn
  calc
    _ = ∏ p ∈ n.primeFactors, (1 - quadraticMonomial k p) := by
      apply Finset.prod_congr rfl
      intro p hp
      simp [quadraticMonomial, (Nat.prime_of_mem_primeFactors hp).ne_zero]
    _ = _ := hh
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [quadraticMonomial, (Nat.pos_of_mem_divisors hd).ne',
        MonoidAlgebra.intCast_def]

/-- Exact cancellation before imposing the two finite cutoffs. -/
theorem quadratic_euler_cancellation {D R : ℕ} (hD : Squarefree D) (hR : Squarefree R)
    (hDR : D.Coprime R) :
    (∑ e ∈ D.divisors, single e (ArithmeticFunction.moebius e)) *
        (∑ b ∈ (D * R).divisors, single b (1 : ℤ)) =
      (∑ u ∈ D.divisors, single (u ^ 2) (ArithmeticFunction.moebius u)) *
        (∑ v ∈ R.divisors, single v (1 : ℤ)) := by
  have hsf : Squarefree (D * R) := (Nat.squarefree_mul hDR).mpr ⟨hD, hR⟩
  have h1 := quadraticMonomial_euler_sub hD 1
  have h2 := quadraticMonomial_euler_add hsf 1
  have h3 := quadraticMonomial_euler_sub hD 2
  have h4 := quadraticMonomial_euler_add hR 1
  simp only [pow_one] at h1 h2 h4
  rw [← h1, ← h2, ← h3, ← h4, hDR.primeFactors_mul,
    Finset.prod_union hDR.disjoint_primeFactors, ← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  rw [show single (p ^ 2) (1 : ℤ) = (single p (1 : ℤ)) ^ 2 by
    simp [pow_two]]
  ring

end Ostmann

end OAI
