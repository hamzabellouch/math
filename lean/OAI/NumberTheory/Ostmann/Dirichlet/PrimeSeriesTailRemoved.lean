import OAI.NumberTheory.Ostmann.Dirichlet.PrimeSeriesTailDivisors

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Dirichlet
open scoped BigOperators

lemma removedPrimeTerm_eq_zero_of_not_mem (M : ℕ) (hM : M ≠ 0) (σ : ℝ)
    (n : ℕ) (hn : n ∉ M.primeFactors) :
    (if n ∣ M then ordinaryPrimeSeriesTerm σ n else 0) = 0 := by
  by_cases hd : n ∣ M
  · rw [ite_eq_left hd]
    have hp : ¬ n.Prime := fun hp => hn (Nat.mem_primeFactors.mpr ⟨hp, hd, hM⟩)
    simp only [ordinaryPrimeSeriesTerm, hp, ite_false]
  · simp only [hd, ite_false]

theorem removedPrimeSeries_summable (M : ℕ) (hM : M ≠ 0) (σ : ℝ) :
    Summable (fun n : ℕ => if n ∣ M then ordinaryPrimeSeriesTerm σ n else 0) :=
  summable_of_ne_finset_zero (s := M.primeFactors) (removedPrimeTerm_eq_zero_of_not_mem M hM σ)

theorem tsum_removedPrimeSeries_eq_primeFactors (M : ℕ) (hM : M ≠ 0) (σ : ℝ) :
    (∑' n : ℕ, if n ∣ M then ordinaryPrimeSeriesTerm σ n else 0) =
      ∑ p ∈ M.primeFactors, ordinaryPrimeSeriesTerm σ p := by
  rw [tsum_eq_sum (removedPrimeTerm_eq_zero_of_not_mem M hM σ)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [ite_eq_left (Nat.mem_primeFactors.mp hp).2.1]

theorem tsum_removedPrimeSeries_le (M : ℕ) (hM : 1 ≤ M) {σ R : ℝ}
    (hσ : 1 ≤ σ) (hR : 1 ≤ R) :
    (∑' n : ℕ, if n ∣ M then ordinaryPrimeSeriesTerm σ n else 0) ≤
      Real.log R + (Real.log 4 + 4) + Real.log M / R := by
  rw [tsum_removedPrimeSeries_eq_primeFactors M (by omega) σ]
  exact sum_prime_divisor_ordinary_le M.primeFactors M hM
    (fun p hp => (Nat.mem_primeFactors.mp hp).1)
    (fun p hp => (Nat.mem_primeFactors.mp hp).2.1) hR hσ

theorem tsum_removedPrimeSeries_le_loglog (M : ℕ) (hM : 1 ≤ M) {σ X C : ℝ}
    (hσ : 1 ≤ σ) (hX : 1 ≤ Real.log X) (hsize : Real.log M ≤ C * Real.log X) :
    (∑' n : ℕ, if n ∣ M then ordinaryPrimeSeriesTerm σ n else 0) ≤
      Real.log (Real.log X) + (Real.log 4 + 4) + C := by
  have h := tsum_removedPrimeSeries_le M hM hσ hX
  have hr : Real.log M / Real.log X ≤ C :=
    (div_le_iff₀ (by linarith : 0 < Real.log X)).mpr hsize
  linarith

end Ostmann.Dirichlet

end

end OAI
