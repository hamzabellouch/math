import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmoothedEnergy
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallKernelScale

namespace OAI

/-! # Exact finite support for the small-kernel Poisson sum -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_pnat_sum_eq_finite (R : ℕ) (f : ℕ → ℂ) (hzero : f 0 = 0)
    (htail : ∀ n, R < n → f n = 0) :
    (∑' n : ℕ+, f n) = ∑ n ∈ Finset.Icc 1 R, f n := by
  rw [tsum_pnat_eq_tsum_of_eq_zero hzero]
  apply tsum_eq_sum
  intro n hn
  by_cases hz : n = 0
  · simpa only [hz] using hzero
  · apply htail
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    omega

theorem quadratic_sieve_weight_square_zero {M b n : ℕ}
    (hM : 0 < M) (hb : 0 < b) (hn : 3 * M < n) :
    quadraticSieveWeight ((n : ℝ) ^ 2 * b / M) = 0 := by
  apply quadraticSieveWeight_eq_zero (Or.inr ?_)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hnR : (3 : ℝ) * M < n := by exact_mod_cast hn
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn₂ : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hprod : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * b := by nlinarith [sq_nonneg (n : ℝ)]
  apply (le_div_iff₀ hMR).mpr
  nlinarith

theorem quadratic_small_square_sum_finite {M b : ℕ} (hM : 0 < M) (hb : 0 < b)
    (q : ℕ) :
    (∑' n : ℕ+, (1 : DirichletCharacter ℂ q) (n : ZMod q) *
      quadraticSieveWeight ((n : ℝ) ^ 2 * b / M)) =
    ∑ n ∈ Finset.Icc 1 (3 * M), (1 : DirichletCharacter ℂ q) (n : ZMod q) *
      quadraticSieveWeight ((n : ℝ) ^ 2 * b / M) := by
  apply quadratic_pnat_sum_eq_finite (3 * M)
    (fun n : ℕ => (1 : DirichletCharacter ℂ q) (n : ZMod q) *
      quadraticSieveWeight ((n : ℝ) ^ 2 * b / M))
  · simp only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_div,
      quadraticSieveWeight_zero, mul_zero]
  · intro n hn
    rw [quadratic_sieve_weight_square_zero hM hb hn, mul_zero]

theorem quadratic_small_kernel_sum_rectangular (R K : ℕ) (f : ℕ → ℂ)
    (htail : ∀ n, R < n → f n = 0) :
    (∑ m ∈ quadraticSmallKernelRange R K, f m) =
      ∑ b ∈ oddSquarefreeRange K, ∑ c ∈ Finset.Icc 1 R,
        if Odd c then f (c ^ 2 * b) else 0 := by
  rw [sum_quadraticSmallKernelRange]
  unfold quadraticSmallKernelPairs
  rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : Odd c
  · by_cases hb : c ^ 2 * b ≤ R
    · simp only [hc, hb, and_self, ite_true]
    · simp only [hc, hb, and_false, ite_false, ite_true,
        htail (c ^ 2 * b) (lt_of_not_ge hb)]
  · simp only [hc, false_and, ite_false]

end Ostmann

end OAI
