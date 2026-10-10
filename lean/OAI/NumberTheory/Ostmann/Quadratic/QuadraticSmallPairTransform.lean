import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmoothedSquareSum
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallKernelCharacter

namespace OAI

/-! # Exact small-kernel pair sum as the positive coprime Poisson sum -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_principal_nat (q n : ℕ) :
    (1 : DirichletCharacter ℂ q) (n : ZMod q) =
      if n.Coprime q then 1 else 0 := by
  by_cases hn : n.Coprime q
  · rw [ite_eq_left hn]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hn)
  · rw [ite_eq_right hn]
    exact (1 : DirichletCharacter ℂ q).map_nonunit
      (fun h => hn ((ZMod.isUnit_iff_coprime n q).mp h))

theorem quadratic_odd_coprime_mask (q n : ℕ) :
    (1 : DirichletCharacter ℂ (2 * q)) (n : ZMod (2 * q)) =
      (if Odd n then (1 : ℂ) else 0) * (if n.Coprime q then 1 else 0) := by
  rw [quadratic_principal_nat]
  simp only [Nat.coprime_mul_iff_right, Nat.coprime_two_right]
  split_ifs <;> simp_all

theorem quadratic_sieve_weight_linear_zero {M n : ℕ} (hM : 0 < M) (hn : 3 * M < n) :
    quadraticSieveWeight ((n : ℝ) / M) = 0 := by
  apply quadraticSieveWeight_eq_zero (Or.inr ?_)
  apply (le_div_iff₀ (show (0 : ℝ) < M by exact_mod_cast hM)).mpr
  have hh : (3 : ℝ) * M < n := by exact_mod_cast hn
  nlinarith [show (0 : ℝ) < M by exact_mod_cast hM]

theorem quadratic_small_pair_transform {M : ℕ} (hM : 0 < M) (K : ℕ)
    {n₁ n₂ : ℕ} (h₁ : Squarefree n₁) (h₂ : Squarefree n₂) :
    (∑ m ∈ quadraticSmallKernelRange (3 * M) K,
      quadraticSieveWeight ((m : ℝ) / M) *
        (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ)) =
    ∑ b ∈ oddSquarefreeRange K,
      ((if b.Coprime (n₁.gcd n₂) then (1 : ℂ) else 0) *
        (jacobiSym b (quadraticPairKernel n₁ n₂) : ℂ)) *
      ∑' c : ℕ+, (1 : DirichletCharacter ℂ (2 * (n₁ * n₂)))
        (c : ZMod (2 * (n₁ * n₂))) *
        quadraticSieveWeight ((c : ℝ) ^ 2 * b / M) := by
  rw [quadratic_small_kernel_sum_rectangular (3 * M) K _ (by
    intro m hm
    rw [quadratic_sieve_weight_linear_zero hM hm, zero_mul, zero_mul])]
  apply Finset.sum_congr rfl
  intro b hb
  have hb₀ : 0 < b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
  rw [quadratic_small_square_sum_finite hM hb₀, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  have hj := jacobi_pair_square_mul c b h₁ h₂
  have hmask := quadratic_odd_coprime_mask (n₁ * n₂) c
  rw [hmask]
  simp only [Nat.cast_mul, Nat.cast_pow] at hj ⊢
  by_cases hc : Odd c
  · simp only [hc, ite_true]
    rw [mul_assoc, hj]
    ring
  · simp only [hc, ite_false, zero_mul, mul_zero]

end Ostmann

end OAI
