import OAI.NumberTheory.Ostmann.Quadratic.QuadraticIterationPowerCost

namespace OAI

/-! # An arbitrarily small loss after the complete finite rough-moment descent -/

namespace Ostmann

theorem quadratic_rough_fixed_depth {ξ η : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hη : 0 < η) {r : ℕ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N K : ℕ,
      0 < M → 0 < N → 0 < K → K ≤ M →
      2 * (2 * (N : ℝ)) ^ 2 * (((M : ℝ) * N) ^ η) ≤ (M : ℝ) * ((K : ℝ) + 1) →
      QuadraticRoughBound M N K
        (C * ((M : ℝ) * N) ^ ((2 * (r : ℝ) + 37) * η + 5 / (r : ℝ)) *
          quadraticDescentScale ξ M N K) := by
  obtain ⟨B, hB, hb⟩ := quadratic_rough_iteration h hξ hξ' hη
  let A := 1 + (η * Real.log 2)⁻¹
  let C := (r : ℝ) * (B * A * 2 ^ η) ^ r * (B * A * 5 ^ 5)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB₀ : 0 < B := lt_of_lt_of_le zero_lt_one hB
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro M N K hM hN hK hKM hcut
  obtain ⟨hD, _, hpow⟩ := quadratic_descent_cutoff_bounds hN hr
  apply (hb M N K (quadraticDescentCutoff N r) r hM hN (by omega) hK hKM hpow hcut).mono_constant
  have hp := mul_le_mul_of_nonneg_right (quadratic_iteration_power_cost hη hB₀ hM hN hr)
    (quadraticDescentScale_nonneg ξ M N K)
  convert hp using 1
  ring

theorem quadratic_rough_power_growth {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ M N K : ℕ,
      0 < M → 0 < N → 0 < K → K ≤ M →
      2 * (2 * (N : ℝ)) ^ 2 * (((M : ℝ) * N) ^ η) ≤ (M : ℝ) * ((K : ℝ) + 1) →
      QuadraticRoughBound M N K
        (C * ((M : ℝ) * N) ^ ε * quadraticDescentScale ξ M N K) := by
  obtain ⟨r, hr⟩ := exists_nat_gt (10 / ε)
  have hr₀ : (0 : ℝ) < r := lt_trans (by positivity : (0 : ℝ) < 10 / ε) hr
  have hrn : 0 < r := by exact_mod_cast hr₀
  let η := ε / (2 * (2 * (r : ℝ) + 37))
  have hη : 0 < η := by dsimp [η]; positivity
  have hcost : (2 * (r : ℝ) + 37) * η + 5 / (r : ℝ) ≤ ε := by
    have heq : (2 * (r : ℝ) + 37) * η = ε / 2 := by
      dsimp [η]
      field_simp
    have hrε : 10 < (r : ℝ) * ε := (div_lt_iff₀ hε).mp hr
    have hdiv : 5 / (r : ℝ) ≤ ε / 2 := (div_le_iff₀ hr₀).mpr (by nlinarith)
    linarith
  obtain ⟨C, hC, hc⟩ := quadratic_rough_fixed_depth h hξ hξ' hη hrn
  have hηε : η ≤ ε := by
    apply div_le_self hε.le
    nlinarith
  refine ⟨η, hη, hηε, C, hC, ?_⟩
  intro M N K hM hN hK hKM hcut
  apply (hc M N K hM hN hK hKM hcut).mono_constant
  have hX : 1 ≤ (M : ℝ) * N := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast hM) (by exact_mod_cast hN)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX hcost) hC.le)
    (quadraticDescentScale_nonneg ξ M N K)

end Ostmann

end OAI
