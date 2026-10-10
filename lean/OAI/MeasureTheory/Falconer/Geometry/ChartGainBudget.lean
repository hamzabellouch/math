import OAI.MeasureTheory.Falconer.Geometry.ProjectionPowerBudget

namespace OAI

/-! The fixed chart costs fit in the reserved weak exponent after a
single dyadic shift. -/
namespace Falconer

theorem chart_gain_budget {θ : ℝ} (hθ : 0 < θ) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < N0 ∧ ∀ n : ℕ, N0 ≤ n+2 →
      400*Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2) ≤
        Real.exp (θ*((n+3:ℕ):ℝ)*Real.log 2) := by
  let ε := min (θ/2) 1
  have hε : 0 < ε := lt_min (by positivity) zero_lt_one
  obtain ⟨N0,hN0,hpoly⟩ := dyadic_quadratic_loss (by positivity : 0 < θ/2)
    (by norm_num : (0:ℝ) ≤ 400)
  refine ⟨ε,N0,hε,min_le_right _ _,hN0,?_⟩
  intro n hn
  have hN : 0 ≤ ((n+2:ℕ):ℝ) := Nat.cast_nonneg _
  have hsq : (1:ℝ) ≤ (((n+2:ℕ):ℝ)+1)^2 := one_le_pow₀ (by linarith only [hN])
  have h400 : (400:ℝ) ≤ Real.exp ((θ/2)*((n+2:ℕ):ℝ)*Real.log 2) :=
    (by nlinarith only [hsq] : (400:ℝ) ≤ 400*(((n+2:ℕ):ℝ)+1)^2).trans (hpoly (n+2) hn)
  have hexp : Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2) ≤
      Real.exp ((θ/2)*((n+2:ℕ):ℝ)*Real.log 2) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hN)
      (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  calc
    _ ≤ Real.exp ((θ/2)*((n+2:ℕ):ℝ)*Real.log 2)*
        Real.exp ((θ/2)*((n+2:ℕ):ℝ)*Real.log 2) :=
      mul_le_mul h400 hexp (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hstep : ((n+2:ℕ):ℝ) ≤ ((n+3:ℕ):ℝ) := by exact_mod_cast (by omega : n+2 ≤ n+3)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hθ.le) hlog

end Falconer

end OAI
