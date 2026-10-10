import OAI.NumberTheory.TotientAsymptotic.CollisionCost

namespace OAI

/-! The published Ford prefactors and tuple recovery fit inside the saving. -/

noncomputable section

namespace TotientAsymptotic

lemma recovery_log_cost_small {h B : ℝ} (hh : 5 ≤ h) (hB : 0 ≤ B) :
    3*(2*B/h^8)*Real.log (h+1) ≤ B/(16*h^4) := by
  have h0 : 0 < h := by linarith
  have hl : Real.log (h+1) ≤ h := by
    simpa using Real.log_le_sub_one_of_pos (by linarith : 0 < h+1)
  have hp : (96 : ℝ) ≤ h^3 := by nlinarith [sq_nonneg (h-5)]
  calc
    _ ≤ 3*(2*B/h^8)*h := mul_le_mul_of_nonneg_left hl (by positivity)
    _ = (6*B)/h^7 := by field_simp; ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ (by positivity : 0 < h^7) (by positivity : 0 < 16*h^4)).mpr
      have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ B*h^4 by positivity)
      convert hm using 1 <;> ring

lemma smooth_log_cost_small {h B Z : ℝ} {b : ℕ}
    (hh : 2 ≤ h) (hb : (b : ℝ) ≤ h) (hB : 0 ≤ B) (hZ : 0 ≤ Z)
    (hZu : Z ≤ 2*B/h^18) : (20*(b : ℝ)*Real.log b+2)*Z ≤ B/(16*h^4) := by
  have h0 : 0 < h := by linarith
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hl := Real.log_le_self hb0
  have hcoef : 20*(b : ℝ)*Real.log b+2 ≤ 22*h^2 := by
    have ht := mul_le_mul_of_nonneg_left hl hb0
    have hsq := pow_le_pow_left₀ hb0 hb 2
    nlinarith
  have hp : (704 : ℝ) ≤ h^12 := by
    have hh12 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hh 12
    norm_num at hh12
    linarith
  calc
    _ ≤ (22*h^2)*(2*B/h^18) := mul_le_mul hcoef hZu hZ (by positivity)
    _ = 44*B/h^16 := by field_simp; ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ (by positivity : 0 < h^16) (by positivity : 0 < 16*h^4)).mpr
      have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ B*h^4 by positivity)
      convert hm using 1 <;> ring

lemma ford_polynomial_prefactor {C B h : ℝ} {b : ℕ}
    (hC : 0 < C) (hB : 0 < B) (hh : 1 ≤ h) (hb : (b : ℝ) ≤ h)
    (hlogB : Real.log B ≤ 26*h) :
    (C*B)^(6*b) ≤ Real.exp (6*(|Real.log C|+26)*h^2) := by
  have hh0 : 0 ≤ h := zero_le_one.trans hh
  have hM : 0 ≤ |Real.log C|+26 := by positivity
  have hl : Real.log (C*B) ≤ (|Real.log C|+26)*h := by
    rw [Real.log_mul hC.ne' hB.ne']
    have hc := le_abs_self (Real.log C)
    have ha := mul_le_mul_of_nonneg_left hh (abs_nonneg (Real.log C))
    nlinarith
  calc
    _ = Real.exp ((6*b : ℕ)*Real.log (C*B)) := by
      rw [Real.exp_nat_mul,Real.exp_log (mul_pos hC hB)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hb0 : (0 : ℝ) ≤ 6*(b : ℝ) := by positivity
      have h1 := mul_le_mul_of_nonneg_left hl hb0
      have h2 := mul_le_mul_of_nonneg_right (show 6*(b : ℝ) ≤ 6*h by linarith)
        (mul_nonneg hM hh0)
      push_cast
      nlinarith

end TotientAsymptotic

end

end OAI
