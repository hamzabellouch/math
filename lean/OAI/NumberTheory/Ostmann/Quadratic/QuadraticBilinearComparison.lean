import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDyadicSelection

namespace OAI

/-! # The divisor-constrained comparison with concrete selected scales

This is the finite comparison of Heath-Brown (1995), Lemma 10. We retain the
explicit number of dyadic bins instead of enlarging the selected scales to
hide logarithms. All quadratic matrix bounds are at the actual shorter ranges.
-/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_dyadic_divisor_mass_bound (M N₁ N₂ D i j : ℕ)
    (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M (N₁ / 2 ^ i) K₁)
    (h₂ : QuadraticSieveBound M (N₂ / 2 ^ j) K₂) (a b : ℕ → ℂ) :
    quadraticDyadicDivisorMass M N₁ N₂ D i j a b ≤
      Real.sqrt (2 * K₁ * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ a) *
      Real.sqrt (2 * K₂ * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ b) := by
  apply le_trans _ (quadratic_dyadic_divisor_family_bound M N₁ N₂ i j
    K₁ K₂ hK₁ hK₂ h₁ h₂ a b)
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro t _
  split_ifs
  · rfl
  · exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

 theorem quadratic_bilinear_comparison (M N₁ N₂ D : ℕ) (a b : ℕ → ℂ)
    (hpos : 0 < ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) :
    ∃ i ≤ Nat.log 2 N₁, ∃ j ≤ Nat.log 2 N₂,
      D < 4 * (2 ^ i * 2 ^ j) ∧ 2 ^ i * 2 ^ j ≤ 2 * D ∧
      ∀ K₁ K₂ : ℝ, 0 ≤ K₁ → 0 ≤ K₂ →
      QuadraticSieveBound M (N₁ / 2 ^ i) K₁ →
      QuadraticSieveBound M (N₂ / 2 ^ j) K₂ →
      (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) ≤
      ((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) *
        (Real.sqrt (2 * K₁ * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ a) *
          Real.sqrt (2 * K₂ * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ b)) := by
  obtain ⟨i, hi, j, hj, _, hD₁, hD₂, hb⟩ := quadratic_divisor_block_selection
    M N₁ N₂ D a b hpos
  refine ⟨i, hi, j, hj, hD₁, hD₂, ?_⟩
  intro K₁ K₂ hK₁ hK₂ h₁ h₂
  exact hb.trans (mul_le_mul_of_nonneg_left
    (quadratic_dyadic_divisor_mass_bound M N₁ N₂ D i j K₁ K₂ hK₁ hK₂ h₁ h₂ a b)
    (by positivity))

 theorem quadratic_bilinear_comparison_epsilon (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N₁ N₂ D : ℕ, ∀ a b : ℕ → ℂ,
    (0 < ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) →
    ∃ i ≤ Nat.log 2 N₁, ∃ j ≤ Nat.log 2 N₂,
      D < 4 * (2 ^ i * 2 ^ j) ∧ 2 ^ i * 2 ^ j ≤ 2 * D ∧
      ∀ K₁ K₂ : ℝ, 0 ≤ K₁ → 0 ≤ K₂ →
      QuadraticSieveBound M (N₁ / 2 ^ i) K₁ →
      QuadraticSieveBound M (N₂ / 2 ^ j) K₂ →
      (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) ≤
      ((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) *
        (Real.sqrt (2 * K₁ * (2 ^ i : ℕ) *
          (C * (N₁ : ℝ) ^ ε * quadraticSieveEnergy N₁ a)) *
        Real.sqrt (2 * K₂ * (2 ^ j : ℕ) *
          (C * (N₂ : ℝ) ^ ε * quadraticSieveEnergy N₂ b))) := by
  obtain ⟨C, hC, hc⟩ := quadratic_divisor_moment_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro M N₁ N₂ D a b hp
  obtain ⟨i, hi, j, hj, hD₁, hD₂, hb⟩ := quadratic_bilinear_comparison M N₁ N₂ D a b hp
  refine ⟨i, hi, j, hj, hD₁, hD₂, ?_⟩
  intro K₁ K₂ hK₁ hK₂ h₁ h₂
  apply (hb K₁ K₂ hK₁ hK₂ h₁ h₂).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hc N₁ a) (by positivity))
  · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hc N₂ b) (by positivity))

end Ostmann

end OAI
