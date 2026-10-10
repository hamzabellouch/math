import OAI.NumberTheory.Ostmann.QuadraticCenter.FullQuadraticCoefficient

namespace OAI

/-! # Uniform errors survive both finite divisor sums -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem sixteenth_divisor_weight_bound (K : ℕ) :
    (1 + 1 / 16 : ℝ) ^ K ≤ Real.exp ((K : ℝ) / 16) := by
  have hb : (1 + 1 / 16 : ℝ) ≤ Real.exp (1 / 16) := by
    linarith [Real.add_one_le_exp (1 / 16 : ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 + 1 / 16) hb K
  simpa only [← Real.exp_nat_mul, div_eq_mul_inv, one_mul] using hp

theorem divisor_combination_difference_bound (Q : Finset ℕ)
    (c f g : Finset ℕ → ℂ) (δ : ℝ) (_hδ : 0 ≤ δ)
    (hc : ∀ U ∈ Q.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card)
    (he : ∀ U ∈ Q.powerset, ‖f U - g U‖ ≤ δ) :
    ‖(∑ U ∈ Q.powerset, c U * f U) - ∑ U ∈ Q.powerset, c U * g U‖ ≤
      δ * (1 + 1 / 16 : ℝ) ^ Q.card := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ U ∈ Q.powerset, δ * (1 / 16 : ℝ) ^ U.card := by
      apply Finset.sum_le_sum
      intro U hU
      rw [norm_mul, mul_comm δ]
      exact mul_le_mul (hc U hU) (he U hU) (norm_nonneg _) (by positivity)
    _ = _ := by rw [← Finset.mul_sum, sum_powerset_power_card]

theorem fullQuadraticCoefficient_difference_bound (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ θ' : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R R' : ℝ) (P : ℕ) (c ξ : Finset ℕ → ℂ) (s : ℕ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hc : ∀ U ∈ Q.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card)
    (hξ : ∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1)
    (he : ∀ V ∈ Q.powerset, ∀ U ∈ Q.powerset,
      ‖primeDivisorMultiples Q hQ D (divisorQuadraticScalar a V) θ Φ R V.toList.prod P U s -
        primeDivisorMultiples Q hQ D (divisorQuadraticScalar a V) θ' Φ R' V.toList.prod P U s‖ ≤ δ) :
    ‖fullQuadraticCoefficient Q hQ D a θ Φ R P c ξ s -
      fullQuadraticCoefficient Q hQ D a θ' Φ R' P c ξ s‖ ≤
      (δ * (1 + 1 / 16 : ℝ) ^ Q.card) *
        ∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹ := by
  let F : Finset ℕ → ℕ → ℂ := fun V s =>
    (∑ U ∈ Q.powerset, c U * primeDivisorMultiples Q hQ D (divisorQuadraticScalar a V) θ Φ R V.toList.prod P U s) -
      ∑ U ∈ Q.powerset, c U * primeDivisorMultiples Q hQ D (divisorQuadraticScalar a V) θ' Φ R' V.toList.prod P U s
  have hd : fullQuadraticCoefficient Q hQ D a θ Φ R P c ξ s -
      fullQuadraticCoefficient Q hQ D a θ' Φ R' P c ξ s =
        divisorWeightedCoefficient Q ξ F s := by
    simp only [fullQuadraticCoefficient, divisorWeightedCoefficient, F, mul_sub,
      Finset.sum_sub_distrib]
  rw [hd]
  exact divisorWeightedCoefficient_norm_le Q ξ F s _ (by positivity) hξ
    (fun V hV => divisor_combination_difference_bound Q c _ _ δ hδ hc (he V hV))

theorem full_coefficient_grid_error_budget (Q : Finset ℕ) (T : ℝ)
    (hT : 0 ≤ T) (hcard : (Q.card : ℝ) ≤ T) (hQ : ∀ p ∈ Q, 1000000 ≤ p) :
    (Real.exp (-128 * T) * (1 + 1 / 16 : ℝ) ^ Q.card) *
      (∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹) ≤ Real.exp (-127 * T) := by
  calc
    _ ≤ (Real.exp (-128 * T) * Real.exp ((Q.card : ℝ) / 16)) *
        Real.exp ((Q.card : ℝ) / 1000) := by
      gcongr
      · exact sixteenth_divisor_weight_bound Q.card
      · exact reciprocal_sqrt_divisor_mass_le Q hQ
    _ = Real.exp (-128 * T + Q.card / 16 + Q.card / 1000) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Ostmann

end OAI
