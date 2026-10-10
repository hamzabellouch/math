import OAI.NumberTheory.Ostmann.Preliminaries.DivisorReciprocalMass
import OAI.NumberTheory.Ostmann.Preliminaries.WeightedNormTriangle

namespace OAI

/-! # Combining the squarefree divisors v in the original coefficients -/

namespace Ostmann

open scoped BigOperators

noncomputable def divisorWeightedCoefficient (Q : Finset ℕ)
    (ξ : Finset ℕ → ℂ) (F : Finset ℕ → ℕ → ℂ) (s : ℕ) : ℂ :=
  ∑ V ∈ Q.powerset, (ξ V * (Real.sqrt (V.toList.prod : ℝ) : ℂ)⁻¹) * F V s

theorem divisor_weight_norm_sum_le (Q : Finset ℕ) (ξ : Finset ℕ → ℂ)
    (hξ : ∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1) :
    (∑ V ∈ Q.powerset, ‖ξ V * (Real.sqrt (V.toList.prod : ℝ) : ℂ)⁻¹‖) ≤
      ∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹ := by
  apply Finset.sum_le_sum
  intro V hV
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_left (by positivity) (hξ V hV)

theorem divisorWeightedCoefficient_norm_le (Q : Finset ℕ)
    (ξ : Finset ℕ → ℂ) (F : Finset ℕ → ℕ → ℂ) (s : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hξ : ∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1)
    (hF : ∀ V ∈ Q.powerset, ‖F V s‖ ≤ B) :
    ‖divisorWeightedCoefficient Q ξ F s‖ ≤
      B * ∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹ := by
  unfold divisorWeightedCoefficient
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ V ∈ Q.powerset, ‖ξ V * (Real.sqrt (V.toList.prod : ℝ) : ℂ)⁻¹‖ * B := by
      apply Finset.sum_le_sum
      intro V hV
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hF V hV) (norm_nonneg _)
    _ ≤ _ := by
      rw [← Finset.sum_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (divisor_weight_norm_sum_le Q ξ hξ) hB

theorem divisorWeightedCoefficient_energy_le (Q : Finset ℕ)
    (ξ : Finset ℕ → ℂ) (F : Finset ℕ → ℕ → ℂ)
    (S : Finset ℕ) (μ : ℕ → ℝ) (B : ℝ)
    (hμ : ∀ s ∈ S, 0 ≤ μ s) (hB : 0 ≤ B)
    (hξ : ∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1)
    (hF : ∀ V ∈ Q.powerset, Real.sqrt (∑ s ∈ S, μ s * ‖F V s‖ ^ 2) ≤ B) :
    Real.sqrt (∑ s ∈ S, μ s * ‖divisorWeightedCoefficient Q ξ F s‖ ^ 2) ≤
      B * ∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹ := by
  apply (sqrt_weighted_sum_energy_le S Q.powerset μ
    (fun V => ξ V * (Real.sqrt (V.toList.prod : ℝ) : ℂ)⁻¹) F B hμ hB hF).trans
  exact mul_le_mul_of_nonneg_left (divisor_weight_norm_sum_le Q ξ hξ) hB

theorem divisorWeightedCoefficient_energy_exp_le (Q : Finset ℕ)
    (ξ : Finset ℕ → ℂ) (F : Finset ℕ → ℕ → ℂ)
    (S : Finset ℕ) (μ : ℕ → ℝ) (B : ℝ)
    (hQ : ∀ p ∈ Q, 1000000 ≤ p) (hμ : ∀ s ∈ S, 0 ≤ μ s) (hB : 0 ≤ B)
    (hξ : ∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1)
    (hF : ∀ V ∈ Q.powerset, Real.sqrt (∑ s ∈ S, μ s * ‖F V s‖ ^ 2) ≤ B) :
    Real.sqrt (∑ s ∈ S, μ s * ‖divisorWeightedCoefficient Q ξ F s‖ ^ 2) ≤
      B * Real.exp ((Q.card : ℝ) / 1000) :=
  (divisorWeightedCoefficient_energy_le Q ξ F S μ B hμ hB hξ hF).trans
    (mul_le_mul_of_nonneg_left (reciprocal_sqrt_divisor_mass_le Q hQ) hB)

end Ostmann

end OAI
