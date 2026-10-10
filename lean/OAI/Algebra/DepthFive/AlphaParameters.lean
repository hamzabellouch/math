import OAI.Algebra.DepthFive.AnalyticParameters
import OAI.Algebra.DepthFive.FractionRounding

namespace OAI

noncomputable section
namespace Problem335.LowerParameters

theorem sqrt_ge_four {n : ℕ} (hn : 16 ≤ n) : 4 ≤ Real.sqrt (n : ℝ) := by
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  exact_mod_cast hn

theorem a_ideal_le {n : ℕ} (_hn : 16 ≤ n) :
    (v n : ℝ) / (Real.sqrt (n : ℝ) - 1) ≤ (a n : ℝ) := Nat.le_ceil _

theorem a_lt_ideal_add_one {n : ℕ} (hn : 16 ≤ n) :
    (a n : ℝ) < (v n : ℝ) / (Real.sqrt (n : ℝ) - 1) + 1 := by
  apply Nat.ceil_lt_add_one
  have hs := sqrt_ge_four hn
  exact div_nonneg (Nat.cast_nonneg _) (by linarith)

theorem a_scale_lower {n : ℕ} (hn : 16 ≤ n) :
    (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) / 4 ≤ (a n : ℝ) := by
  have hs := sqrt_ge_four hn
  have hden : 0 < Real.sqrt (n : ℝ) - 1 := by linarith
  have hv : 3 * (n : ℝ) ^ 3 ≤ 8 * (v n : ℝ) := by
    exact_mod_cast three_mul_cube_le_eight_mul_v hn
  have heq : (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) ^ 3 := by
    calc
      _ = (n : ℝ) ^ 2 * (Real.sqrt (n : ℝ)) ^ 2 := by ring
      _ = (n : ℝ) ^ 3 := by rw [Real.sq_sqrt (by positivity)]; ring
  apply le_trans _ (a_ideal_le hn)
  apply (le_div_iff₀ hden).mpr
  have hnonneg : 0 ≤ (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by positivity
  nlinarith

theorem a_scale_upper {n : ℕ} (hn : 16 ≤ n) :
    (a n : ℝ) ≤ 3 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by
  have hs := sqrt_ge_four hn
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < Real.sqrt (n : ℝ) - 1 := by linarith
  have hv : (v n : ℝ) ≤ (n : ℝ) ^ 3 := by exact_mod_cast v_le_cube n
  have heq : (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) ^ 3 := by
    calc
      _ = (n : ℝ) ^ 2 * (Real.sqrt (n : ℝ)) ^ 2 := by ring
      _ = (n : ℝ) ^ 3 := by rw [Real.sq_sqrt (by positivity)]; ring
  have hnonneg : 0 ≤ (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ Real.sqrt (n : ℝ) by linarith) hnonneg
  have hideal : (v n : ℝ) / (Real.sqrt (n : ℝ) - 1) ≤
      2 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hlarge : 1 ≤ (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by
    have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ Real.sqrt (n : ℝ) by linarith)
      (sq_nonneg (n : ℝ))]
  have hround := a_lt_ideal_add_one hn
  nlinarith

theorem alpha_bounds {n : ℕ} (hn : 16 ≤ n) :
    1 / Real.sqrt (n : ℝ) ≤ alpha n ∧
      alpha n ≤ 1 / Real.sqrt (n : ℝ) *
        Real.exp ((Real.sqrt (n : ℝ) - 1) / (v n : ℝ)) := by
  have hs := sqrt_ge_four hn
  have hv : (0 : ℝ) < v n := by exact_mod_cast v_pos (by omega : 4 ≤ n)
  exact fraction_natCeil_inverse_bounds (by linarith) hv

/-- The relative logarithmic rounding error is controlled by the rounded order. -/
theorem alpha_log_error_bounds {n : ℕ} (hn : 16 ≤ n) :
    0 ≤ Real.log (alpha n * Real.sqrt (n : ℝ)) ∧
      Real.log (alpha n * Real.sqrt (n : ℝ)) ≤ 2 / (a n : ℝ) := by
  have hs := sqrt_ge_four hn
  have hsm : 0 < Real.sqrt (n : ℝ) - 1 := by linarith
  have hspos : 0 < Real.sqrt (n : ℝ) := by linarith
  have hv : (0 : ℝ) < v n := by exact_mod_cast v_pos (by omega : 4 ≤ n)
  have hx : 0 < (v n : ℝ) / (Real.sqrt (n : ℝ) - 1) := div_pos hv hsm
  have hxa := a_ideal_le hn
  have hax := a_lt_ideal_add_one hn
  have ha : 4 * (n : ℝ) ≤ (a n : ℝ) := by exact_mod_cast four_mul_n_le_a hn
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hxone : 1 ≤ (v n : ℝ) / (Real.sqrt (n : ℝ) - 1) := by linarith
  have hbase : ((v n : ℝ) / (Real.sqrt (n : ℝ) - 1)) /
      ((v n : ℝ) / (Real.sqrt (n : ℝ) - 1) + (v n : ℝ)) =
      1 / Real.sqrt (n : ℝ) := by
    field_simp
    ring
  have heq : ((a n : ℝ) / ((a n : ℝ) + (v n : ℝ))) /
      (((v n : ℝ) / (Real.sqrt (n : ℝ) - 1)) /
      ((v n : ℝ) / (Real.sqrt (n : ℝ) - 1) + (v n : ℝ))) =
      alpha n * Real.sqrt (n : ℝ) := by
    rw [hbase, alpha]
    field_simp
  constructor
  · rw [← heq]
    exact (fraction_rounding_log_bounds hx hv hxa hax.le).1
  · rw [← heq]
    exact fraction_rounding_log_le_two_div hxone hv hxa hax.le

/-- The occupation-moment error from differentiation is of order `n^(-1/2)`. -/
theorem sq_div_a_le {n : ℕ} (hn : 16 ≤ n) :
    (n : ℝ) ^ 2 / (a n : ℝ) ≤ 4 / Real.sqrt (n : ℝ) := by
  have ha : (0 : ℝ) < a n := by exact_mod_cast a_pos (by omega : 4 ≤ n)
  have hs : 0 < Real.sqrt (n : ℝ) := by have := sqrt_ge_four hn; linarith
  apply (div_le_div_iff₀ ha hs).mpr
  have h := a_scale_lower hn
  linarith

/-- The ambient-variable occupation error has the better order `1/n`. -/
theorem sq_div_v_le {n : ℕ} (hn : 16 ≤ n) :
    (n : ℝ) ^ 2 / (v n : ℝ) ≤ 8 / (3 * (n : ℝ)) := by
  have hv : (0 : ℝ) < v n := by exact_mod_cast v_pos (by omega : 4 ≤ n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  apply (div_le_div_iff₀ hv (by positivity)).mpr
  have h : 3 * (n : ℝ) ^ 3 ≤ 8 * (v n : ℝ) := by
    exact_mod_cast three_mul_cube_le_eight_mul_v hn
  nlinarith

/-- Uniform two-sided growth of the chosen differentiation order. -/
theorem a_isTheta :
    Asymptotics.IsTheta Filter.atTop (fun n : ℕ => (a n : ℝ))
      (fun n : ℕ => (n : ℝ) ^ 2 * Real.sqrt (n : ℝ)) := by
  constructor
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨3, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 16] with n hn
    have hnonneg : 0 ≤ (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (a n : ℝ) by positivity),
      abs_of_nonneg hnonneg, mul_assoc] using a_scale_upper hn
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨4, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 16] with n hn
    have hnonneg : 0 ≤ (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by positivity
    simp only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (a n : ℝ) by positivity), abs_of_nonneg hnonneg]
    have h := a_scale_lower hn
    linarith

end Problem335.LowerParameters

end

end OAI
