import OAI.Algebra.DepthFive.AnalyticParameters
import OAI.Algebra.DepthFive.FractionRounding
import OAI.Algebra.DepthFive.PowerPerturbation

namespace OAI

/-! Assembly of the numerical inequalities for the actual rank parameters. -/
noncomputable section
namespace Problem335.LowerParameters

theorem n_le_a0 {n : ℕ} (hn : 4 ≤ n) : (n : ℝ) ≤ a0 n := by
  have hk : (1 : ℝ) ≤ k n := by exact_mod_cast k_pos hn
  calc
    (n : ℝ) ≤ (k n : ℝ) * (n : ℝ) := by nlinarith
    _ ≤ a0 n := k_mul_n_le_a0 hn

theorem n_le_b0 {n : ℕ} (hn : 4 ≤ n) : (n : ℝ) ≤ b0 n :=
  ((n_le_a0 hn).trans (a0_le_a n)).trans (a_le_b0 hn)

theorem alpha_le_inv_sqrt_mul_exp {n : ℕ} (hn : 4 ≤ n) :
    alpha n ≤ (Real.sqrt (n : ℝ))⁻¹ * Real.exp (1 / (n : ℝ)) := by
  have hs := sqrt_ge_two hn
  have hv : (0 : ℝ) < v n := by exact_mod_cast v_pos hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hraw : alpha n ≤ (Real.sqrt (n : ℝ))⁻¹ *
      Real.exp ((Real.sqrt (n : ℝ) - 1) / (v n : ℝ)) := by
    simpa [alpha, a, a0, one_div] using
      (fraction_natCeil_inverse_bounds (by linarith : 1 < Real.sqrt (n : ℝ)) hv).2
  have herr : (Real.sqrt (n : ℝ) - 1) / (v n : ℝ) ≤ 1 / (n : ℝ) := by
    have h := one_div_le_one_div_of_le hn' (n_le_a0 hn)
    simpa [a0, one_div_div] using h
  exact hraw.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr herr)
    (by positivity))

theorem alpha_le_rpow_mul_exp {n : ℕ} (hn : 4 ≤ n) :
    alpha n ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (1 / (n : ℝ)) := by
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  exact alpha_le_inv_sqrt_mul_exp hn

theorem beta_le_rpow_mul_exp {n : ℕ} (hn : 4 ≤ n) :
    beta n ≤ (alpha n) ^ (rho n) * Real.exp (1 / (n : ℝ)) := by
  have hu : (0 : ℝ) < u n := by exact_mod_cast u_pos hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hraw : beta n ≤ (alpha n) ^ (rho n) *
      Real.exp ((1 - (alpha n) ^ (rho n)) / ((u n : ℝ) * (alpha n) ^ (rho n))) := by
    simpa [beta, b, b0] using (fraction_natCeil_target_bounds
      (alpha_rpow_rho_pos hn) (alpha_rpow_rho_lt_one hn) hu).2
  have herr : (1 - (alpha n) ^ (rho n)) / ((u n : ℝ) * (alpha n) ^ (rho n)) ≤
      1 / (n : ℝ) := by
    have h := one_div_le_one_div_of_le hn' (n_le_b0 hn)
    simpa [b0, one_div_div] using h
  exact hraw.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr herr)
    (alpha_rpow_rho_pos hn).le)

theorem one_sub_rho_le_two_div_sqrt {n : ℕ} (hn : 4 ≤ n) :
    1 - rho n ≤ 2 / Real.sqrt (n : ℝ) := by
  have hm : (0 : ℝ) < m n := by exact_mod_cast m_pos hn
  have hs := sqrt_ge_two hn
  have hsn := s_le_sqrt n
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hnm : (n : ℝ) ≤ 2 * (m n : ℝ) := by exact_mod_cast n_le_two_mul_m n
  rw [one_sub_rho hn]
  apply (div_le_div_iff₀ hm (by linarith)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hsn (Real.sqrt_nonneg (n : ℝ))]

theorem one_sub_rho_le_four_div_sqrt {n : ℕ} (hn : 4 ≤ n) :
    1 - rho n ≤ 4 / Real.sqrt (n : ℝ) := by
  exact (one_sub_rho_le_two_div_sqrt hn).trans
    (div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _))

theorem eventually_q_beta_le_two_div_sqrt :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      q n ≤ 2 / Real.sqrt (n : ℝ) ∧ beta n ≤ 2 / Real.sqrt (n : ℝ) := by
  obtain ⟨n₀, h⟩ := PowerPerturbation.eventually_q_beta_bounds
  refine ⟨max n₀ 4, fun n hn => ?_⟩
  have hn4 : 4 ≤ n := (le_max_right _ _).trans hn
  exact h n ((le_max_left _ _).trans hn) (alpha n) (rho n) (beta n)
    (alpha_pos hn4) (alpha_le_rpow_mul_exp hn4)
    (rho_pos hn4).le (rho_lt_one hn4).le
    (one_sub_rho_le_four_div_sqrt hn4) (beta_le_rpow_mul_exp hn4)

/-- The explicit inequalities from the parameter lemma that are consumed by
both circuit-rank and moment estimates.  All are asserted for the same `n`. -/
structure Admissible (n : ℕ) : Prop where
  n_ge_sixteen : 16 ≤ n
  s_lower : Real.sqrt (n : ℝ) / 2 ≤ (s n : ℝ)
  s_upper : (s n : ℝ) ≤ Real.sqrt (n : ℝ)
  lambda_lower : (3 : ℝ) / 8 ≤ lambda n
  rho_positive : 0 < rho n
  rho_lt_one : rho n < 1
  a_ge_k : k n ≤ a n
  a_ge_four_n : 4 * n ≤ a n
  b_ge_four_n : 4 * n ≤ b n
  alpha_positive : 0 < alpha n
  alpha_lt_one : alpha n < 1
  alpha_lower : (Real.sqrt (n : ℝ))⁻¹ ≤ alpha n
  alpha_inverse_upper : (alpha n)⁻¹ ≤ Real.sqrt (n : ℝ)
  beta_lower : (alpha n) ^ (rho n) ≤ beta n
  beta_upper : beta n ≤ 2 / Real.sqrt (n : ℝ)
  q_lower : (Real.sqrt (n : ℝ))⁻¹ ≤ q n
  q_upper : q n ≤ 2 / Real.sqrt (n : ℝ)
  sqrt_upper_power : 2 / Real.sqrt (n : ℝ) ≤ (n : ℝ) ^ (-(2 / 5 : ℝ))
  sqrt_upper_half : 2 / Real.sqrt (n : ℝ) ≤ 1 / 2

theorem eventually_admissible : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Admissible n := by
  obtain ⟨n₁, h₁⟩ := eventually_q_beta_le_two_div_sqrt
  obtain ⟨n₂, h₂⟩ := PowerPerturbation.eventually_inverse_sqrt_bounds
  refine ⟨max (max n₁ n₂) 16, fun n hn => ?_⟩
  have hn16 : 16 ≤ n := (le_max_right _ _).trans hn
  have hn4 : 4 ≤ n := by omega
  have hn1 : n₁ ≤ n := (le_max_left n₁ n₂).trans ((le_max_left _ _).trans hn)
  have hn2 : n₂ ≤ n := (le_max_right n₁ n₂).trans ((le_max_left _ _).trans hn)
  exact ⟨hn16, sqrt_half_le_s hn16, s_le_sqrt n, lambda_ge_three_eighths hn16,
    rho_pos hn4, rho_lt_one hn4, k_le_a hn4, four_mul_n_le_a hn16,
    four_mul_n_le_b hn16, alpha_pos hn4, alpha_lt_one hn4, inv_sqrt_le_alpha hn4,
    inv_alpha_le_sqrt hn4, alpha_rpow_rho_le_beta hn4, (h₁ n hn1).2,
    inv_sqrt_le_q hn4, (h₁ n hn1).1, (h₂ n hn2).1, (h₂ n hn2).2⟩

end Problem335.LowerParameters

end

end OAI
