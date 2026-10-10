import Mathlib

namespace OAI
noncomputable section
open Filter

lemma bounded_geometric_absorption (s : ℕ → ℝ) (M A : ℝ) (hA : 0≤A)
    (hM : ∀ n, s n≤M) (hr : ∀ n, s n≤(1/64)*s (n+1)+A*32^n) :
    s 0≤2*A := by
  have htel : ∀ n, s 0≤(1/64:ℝ)^n*s n+2*A*(1-(1/2:ℝ)^n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hz := mul_le_mul_of_nonneg_left (hr n) (by positivity : (0:ℝ)≤(1/64:ℝ)^n)
      have hp : (1/64:ℝ)^n*32^n=(1/2:ℝ)^n := by rw [←mul_pow]; norm_num
      rw [pow_succ, pow_succ]
      nlinarith
  have hh (n : ℕ) : s 0≤(1/64:ℝ)^n*M+2*A := by
    have := mul_le_mul_of_nonneg_left (hM n) (by positivity : (0:ℝ)≤(1/64:ℝ)^n)
    have hz : 0≤2*A*(1/2:ℝ)^n := by positivity
    nlinarith [htel n]
  have hl := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0:ℝ)≤1/64) (by norm_num : (1/64:ℝ)<1)).mul_const M
  have hl := hl.add_const (2*A)
  simp only [zero_mul,zero_add] at hl
  exact ge_of_tendsto hl (Eventually.of_forall hh)

end

end OAI
