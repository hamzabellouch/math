import Mathlib

namespace OAI
noncomputable section
open Filter

lemma bounded_geometric_absorption_general (B : ℝ) (hB : 1≤B)
    (s : ℕ → ℝ) (M A : ℝ) (hA : 0≤A) (hM : ∀ n, s n≤M)
    (hr : ∀ n, s n≤(1/(2*B))*s (n+1)+A*B^n) : s 0≤2*A := by
  have hBp : 0<B := lt_of_lt_of_le zero_lt_one hB
  have hθ : 0≤1/(2*B) := by positivity
  have hθ1 : 1/(2*B)<1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hprod : (1/(2*B))*B=(1/2:ℝ) := by field_simp
  have htel : ∀ n, s 0≤(1/(2*B):ℝ)^n*s n+2*A*(1-(1/2:ℝ)^n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hz := mul_le_mul_of_nonneg_left (hr n) (pow_nonneg hθ n)
      have hp : (1/(2*B):ℝ)^n*B^n=(1/2:ℝ)^n := by rw [←mul_pow,hprod]
      rw [pow_succ,pow_succ]
      nlinarith
  have hh (n : ℕ) : s 0≤(1/(2*B):ℝ)^n*M+2*A := by
    have := mul_le_mul_of_nonneg_left (hM n) (pow_nonneg hθ n)
    have hz : 0≤2*A*(1/2:ℝ)^n := by positivity
    nlinarith [htel n]
  have hl := ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθ1).mul_const M).add_const (2*A)
  simp only [zero_mul,zero_add] at hl
  exact ge_of_tendsto hl (Eventually.of_forall hh)

end

end OAI
