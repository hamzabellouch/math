import OAI.NumberTheory.Ostmann.Quadratic.QuadraticWeightedBilinear

namespace OAI

/-! # A uniform bound over the finitely many actual divisor scales -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_bilinear_uniform_bound (M N₁ N₂ D : ℕ) (a b : ℕ → ℂ)
    (K₁ K₂ : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hK₁ : ∀ i ≤ Nat.log 2 N₁, 0 ≤ K₁ i)
    (hK₂ : ∀ j ≤ Nat.log 2 N₂, 0 ≤ K₂ j)
    (h₁ : ∀ i ≤ Nat.log 2 N₁, QuadraticSieveBound M (N₁ / 2 ^ i) (K₁ i))
    (h₂ : ∀ j ≤ Nat.log 2 N₂, QuadraticSieveBound M (N₂ / 2 ^ j) (K₂ j))
    (hcost : ∀ i ≤ Nat.log 2 N₁, ∀ j ≤ Nat.log 2 N₂,
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ a) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ b) ≤ T) :
    (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) ≤
      ((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) * T := by
  by_cases hp : 0 < ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d a b m‖
  · obtain ⟨i, hi, j, hj, hD₁, hD₂, hb⟩ := quadratic_bilinear_comparison M N₁ N₂ D a b hp
    exact (hb (K₁ i) (K₂ j) (hK₁ i hi) (hK₂ j hj) (h₁ i hi) (h₂ j hj)).trans
      (mul_le_mul_of_nonneg_left (hcost i hi j hj hD₁ hD₂) (by positivity))
  · exact (le_of_not_gt hp).trans (by positivity)

 theorem quadratic_log_modulated_uniform_bound (M N₁ N₂ D : ℕ) (a b : ℕ → ℂ)
    (K₁ K₂ : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hK₁ : ∀ i ≤ Nat.log 2 N₁, 0 ≤ K₁ i)
    (hK₂ : ∀ j ≤ Nat.log 2 N₂, 0 ≤ K₂ j)
    (h₁ : ∀ i ≤ Nat.log 2 N₁, QuadraticSieveBound M (N₁ / 2 ^ i) (K₁ i))
    (h₂ : ∀ j ≤ Nat.log 2 N₂, QuadraticSieveBound M (N₂ / 2 ^ j) (K₂ j))
    (hcost : ∀ i ≤ Nat.log 2 N₁, ∀ j ≤ Nat.log 2 N₂,
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ a) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ b) ≤ T)
    (u : ℝ) :
    (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d
        (quadraticLogModulate u a) (quadraticLogModulate (-u) b) m‖) ≤
      ((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) * T := by
  apply quadratic_bilinear_uniform_bound M N₁ N₂ D _ _ K₁ K₂ T hT hK₁ hK₂ h₁ h₂
  intro i hi j hj hD₁ hD₂
  rw [quadraticDivisorMoment_logModulate, quadraticDivisorMoment_logModulate]
  exact hcost i hi j hj hD₁ hD₂

end Ostmann

end OAI
