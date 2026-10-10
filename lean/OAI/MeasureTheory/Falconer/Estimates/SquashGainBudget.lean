import OAI.MeasureTheory.Falconer.Geometry.NormalizedGainBudget

namespace OAI

/-! Fixed losses in the slope normalization fit inside the reserved gain. -/
namespace Falconer

theorem squash_gain_budget {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < N0 ∧ ∀ n : ℕ, N0 ≤ n+2 →
      20736*Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2) ≤
        Real.exp (θ*((n+3:ℕ):ℝ)*Real.log 2) ∧
      81 ≤ (1/(2:ℝ)^(2*n))^(-η/2) := by
  let ε := min (θ/2) 1
  have hε : 0 < ε := lt_min (by positivity) zero_lt_one
  obtain ⟨N1,_,hconst⟩ := dyadic_quadratic_loss
    (lt_min (half_pos hθ) (half_pos hη)) (by norm_num : (0:ℝ) ≤ 20736)
  refine ⟨ε,max 4 N1,hε,min_le_right _ _,lt_of_lt_of_le (by norm_num : 0 < 4) (le_max_left _ _),?_⟩
  intro n hn
  have hn2 : 2 ≤ n := by have := (le_max_left 4 N1).trans hn; omega
  have hnR : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hmR : 0 ≤ ((n+2:ℕ):ℝ) := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hfixed : 20736 ≤ Real.exp ((min (θ/2) (η/2))*((n+2:ℕ):ℝ)*Real.log 2) := by
    apply le_trans _ (hconst (n+2) ((le_max_right _ _).trans hn))
    have hs : (1:ℝ) ≤ (((n+2:ℕ):ℝ)+1)^2 := one_le_pow₀ (by linarith only [hmR])
    nlinarith only [hs]
  have hfirst : 20736 ≤ Real.exp ((θ/2)*((n+2:ℕ):ℝ)*Real.log 2) := by
    apply hfixed.trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hmR) hlog
  have hsecond : 81 ≤ Real.exp ((η/2)*((n+2:ℕ):ℝ)*Real.log 2) := by
    apply (show (81:ℝ) ≤ 20736 by norm_num).trans (hfixed.trans _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_right _ _) hmR) hlog
  constructor
  · calc
      _ ≤ Real.exp ((θ/2)*((n+2:ℕ):ℝ)*Real.log 2)*
          Real.exp ((θ/2)*((n+2:ℕ):ℝ)*Real.log 2) := by
        apply mul_le_mul hfirst _ (Real.exp_pos _).le (Real.exp_pos _).le
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (min_le_left _ _) hmR) hlog
      _ = Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        gcongr
        norm_num
  · apply hsecond.trans
    rw [show (1/(2:ℝ)^(2*n)) = (1/(2:ℝ))^(2*n) by rw [div_pow,one_pow],half_power_rpow_exp]
    apply Real.exp_le_exp.mpr
    push_cast
    apply mul_le_mul_of_nonneg_right _ hlog
    have hnR2 : (2:ℝ) ≤ n := by exact_mod_cast hn2
    nlinarith only [mul_nonneg hη.le (sub_nonneg.mpr hnR2)]

end Falconer

end OAI
