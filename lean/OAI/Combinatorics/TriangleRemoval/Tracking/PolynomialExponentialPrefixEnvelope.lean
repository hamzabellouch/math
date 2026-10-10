import Mathlib

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem polynomial_exponential_le_prefix_envelope (A K κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop,
      A*(n : ℝ)^K*Real.exp (-(n : ℝ)^κ) ≤
        Real.exp (-(Real.log n)^(4/3 : ℝ)) := by
  have ho := ((isLittleO_log_rpow_atTop hκ).const_mul_left (K+1)).add
    (isLittleO_log_rpow_rpow_atTop (4/3 : ℝ) hκ)
  have hbound := (ho.comp_tendsto tendsto_natCast_atTop_atTop).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hbound, tendsto_natCast_atTop_atTop.eventually_ge_atTop A,
    eventually_ge_atTop (1 : ℕ)] with n hn hA hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hb : (K+1)*Real.log (n : ℝ)+(Real.log n)^(4/3 : ℝ) ≤ (n : ℝ)^κ := by
    dsimp at hn
    simp only [one_mul] at hn
    rw [abs_of_nonneg (Real.rpow_nonneg hn0.le κ)] at hn
    exact (le_abs_self _).trans hn
  calc
    _ ≤ (n : ℝ)*(n : ℝ)^K*Real.exp (-(n : ℝ)^κ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA
        (Real.rpow_nonneg hn0.le K)) (Real.exp_pos _).le
    _ = Real.exp (Real.log n*(K+1)-(n : ℝ)^κ) := by
      rw [show (n : ℝ)*(n : ℝ)^K = (n : ℝ)^(K+1) by
        rw [Real.rpow_add hn0,Real.rpow_one]; ring]
      rw [Real.rpow_def_of_pos hn0,← Real.exp_add]
      congr 1
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hb])

end SharpTerminalLeave

end

end OAI
