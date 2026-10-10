import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDivisorDyadicPartition
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticUnitDivisor
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticUniformGauss

namespace OAI

/-! # Whole divisor sums from the actual shorter quadratic matrices -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_divisor_mass_from_blocks {Q : ℕ} (hQ : 1 ≤ Q)
    (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d) (A : ℝ) (T : ℕ → ℝ)
    (hunit : F 1 ≤ A)
    (hblocks : ∀ j < Nat.log 2 Q + 1,
      (∑ d ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), F d) ≤ T j) :
    (∑ d ∈ Finset.Icc 1 Q, F d) ≤ A + ∑ j ∈ Finset.range (Nat.log 2 Q + 1), T j := by
  rw [quadratic_divisor_sum_one_blocks hQ]
  apply add_le_add hunit
  apply Finset.sum_le_sum
  intro j hj
  apply le_trans _ (hblocks j (Finset.mem_range.mp hj))
  exact Finset.sum_le_sum_of_subset_of_nonneg (quadraticDivisorDyadicBlock_subset Q j)
    (fun d _ _ => hF d)

theorem quadratic_whole_divisor_bound (M N₁ N₂ Q : ℕ) (hQ : 1 ≤ Q)
    (a b : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℕ → ℝ)
    (hT : ∀ j < Nat.log 2 Q + 1, 0 ≤ T j)
    (hK₁ : ∀ i ≤ Nat.log 2 N₁, 0 ≤ K₁ i)
    (hK₂ : ∀ i ≤ Nat.log 2 N₂, 0 ≤ K₂ i)
    (h₁ : ∀ i ≤ Nat.log 2 N₁, QuadraticSieveBound M (N₁ / 2 ^ i) (K₁ i))
    (h₂ : ∀ i ≤ Nat.log 2 N₂, QuadraticSieveBound M (N₂ / 2 ^ i) (K₂ i))
    (hcost : ∀ r < Nat.log 2 Q + 1, ∀ i ≤ Nat.log 2 N₁, ∀ j ≤ Nat.log 2 N₂,
      2 ^ r < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * 2 ^ r →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ a) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ b) ≤ T r) :
    (∑ d ∈ Finset.Icc 1 Q, ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) ≤
      Real.sqrt (2 * K₁ 0 * quadraticDivisorMoment N₁ a) *
        Real.sqrt (2 * K₂ 0 * quadraticDivisorMoment N₂ b) +
      (((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1)) *
        ∑ r ∈ Finset.range (Nat.log 2 Q + 1), T r := by
  have hu := quadratic_unit_divisor_bound M N₁ N₂ (K₁ 0) (K₂ 0)
    (hK₁ 0 (Nat.zero_le _)) (hK₂ 0 (Nat.zero_le _))
    (by simpa only [pow_zero, Nat.div_one] using h₁ 0 (Nat.zero_le _))
    (by simpa only [pow_zero, Nat.div_one] using h₂ 0 (Nat.zero_le _)) a b
  have hb (r : ℕ) (hr : r < Nat.log 2 Q + 1) :=
    quadratic_bilinear_uniform_bound M N₁ N₂ (2 ^ r) a b K₁ K₂ (T r) (hT r hr)
      hK₁ hK₂ h₁ h₂ (hcost r hr)
  have hh := quadratic_divisor_mass_from_blocks hQ
    (fun d => ∑ m ∈ oddSquarefreeRange M, ‖quadraticDivisorBilinear N₁ N₂ d a b m‖)
    (fun _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) _ _ hu hb
  simpa only [← Finset.mul_sum, mul_assoc] using hh

theorem quadratic_whole_gauss_divisor_bound (M N₁ N₂ Q : ℕ) (hQ : 1 ≤ Q)
    (a b : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℕ → ℝ)
    (hT : ∀ j < Nat.log 2 Q + 1, 0 ≤ T j)
    (hK₁ : ∀ i ≤ Nat.log 2 N₁, 0 ≤ K₁ i)
    (hK₂ : ∀ i ≤ Nat.log 2 N₂, 0 ≤ K₂ i)
    (h₁ : ∀ i ≤ Nat.log 2 N₁, QuadraticSieveBound M (N₁ / 2 ^ i) (K₁ i))
    (h₂ : ∀ i ≤ Nat.log 2 N₂, QuadraticSieveBound M (N₂ / 2 ^ i) (K₂ i))
    (hcost : ∀ r < Nat.log 2 Q + 1, ∀ i ≤ Nat.log 2 N₁, ∀ j ≤ Nat.log 2 N₂,
      2 ^ r < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * 2 ^ r →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ a) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ b) ≤ T r) :
    (∑ d ∈ Finset.Icc 1 Q, ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticGaussDivisorBilinear N₁ N₂ d a b m‖) ≤
      3 * (Real.sqrt (2 * K₁ 0 * quadraticDivisorMoment N₁ a) *
        Real.sqrt (2 * K₂ 0 * quadraticDivisorMoment N₂ b)) +
      3 * (((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1)) *
        ∑ r ∈ Finset.range (Nat.log 2 Q + 1), T r := by
  have hu := quadratic_gauss_unit_divisor_bound M N₁ N₂ (K₁ 0) (K₂ 0)
    (hK₁ 0 (Nat.zero_le _)) (hK₂ 0 (Nat.zero_le _))
    (by simpa only [pow_zero, Nat.div_one] using h₁ 0 (Nat.zero_le _))
    (by simpa only [pow_zero, Nat.div_one] using h₂ 0 (Nat.zero_le _)) a b
  have hb (r : ℕ) (hr : r < Nat.log 2 Q + 1) :=
    quadratic_gauss_uniform_bound M N₁ N₂ (2 ^ r) a b K₁ K₂ (T r) (hT r hr)
      hK₁ hK₂ h₁ h₂ (hcost r hr)
  have hh := quadratic_divisor_mass_from_blocks hQ
    (fun d => ∑ m ∈ oddSquarefreeRange M, ‖quadraticGaussDivisorBilinear N₁ N₂ d a b m‖)
    (fun _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) _ _ hu hb
  simpa only [← Finset.mul_sum, mul_assoc] using hh

end Ostmann

end OAI
