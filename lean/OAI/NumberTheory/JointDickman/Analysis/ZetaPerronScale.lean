import OAI.NumberTheory.JointDickman.Analysis.ZetaContourRegion

namespace OAI

/-! # A concrete height and width for fixed-order Perron estimates -/
namespace JointDickman

noncomputable def perronScaleWidth (A q : ℝ) : ℝ :=
  zetaContourWidth A (Real.exp q) / 4

theorem perronScale_log_bound {q : ℝ} (hq : 2 ≤ q) :
    1+Real.log (Real.exp q+3) ≤ 2*q := by
  have he : 3 ≤ Real.exp q := by linarith [Real.add_one_le_exp q]
  have he1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hlog : Real.log (Real.exp q+3) ≤ q+1 := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    rw [Real.exp_add]
    nlinarith
  linarith

theorem perronScaleWidth_pos {A q : ℝ} (hA : 0 < A) : 0 < perronScaleWidth A q := by
  have hlog : 0 < Real.log (Real.exp q+3) := Real.log_pos (by linarith [Real.exp_pos q])
  unfold perronScaleWidth zetaContourWidth
  positivity

theorem perronScaleWidth_mul_lower {A q : ℝ} (hA : 0 < A) (hq : 2 ≤ q) :
    A/2048*q ≤ q^10*perronScaleWidth A q := by
  have hq0 : 0 < q := by linarith
  have hlog : 0 < Real.log (Real.exp q+3) := Real.log_pos (by linarith [Real.exp_pos q])
  have hD : 0 < (1+Real.log (Real.exp q+3))^9 := by positivity
  have hDle := pow_le_pow_left₀ (by linarith : 0 ≤ 1+Real.log (Real.exp q+3))
    (perronScale_log_bound hq) 9
  have hw : A/(4*(2*q)^9) ≤ perronScaleWidth A q := by
    unfold perronScaleWidth zetaContourWidth
    rw [div_div]
    apply div_le_div_of_nonneg_left hA.le (mul_pos hD (by norm_num))
    nlinarith
  calc
    A/2048*q = q^10*(A/(4*(2*q)^9)) := by
      field_simp
      ring
    _ ≤ q^10*perronScaleWidth A q := mul_le_mul_of_nonneg_left hw (pow_nonneg hq0.le _)

theorem perronScale_right_le_width {A q : ℝ} (hA : 0 < A)
    (hq : 2 ≤ q) (hqA : 2048/A ≤ q) :
    1/q^10 ≤ perronScaleWidth A q := by
  have hq0 : 0 < q := by linarith
  apply (div_le_iff₀ (pow_pos hq0 10)).mpr
  have hAq : 2048 ≤ q*A := (div_le_iff₀ hA).mp hqA
  have hlower := perronScaleWidth_mul_lower hA hq
  nlinarith

theorem perronScaleWidth_upper {A q : ℝ} (hA : 0 ≤ A) (hq : 2 ≤ q) :
    perronScaleWidth A q ≤ A/(4*q) := by
  have hq0 : 0 < q := by linarith
  have hlog : q ≤ Real.log (Real.exp q+3) := by
    have h := Real.log_le_log (Real.exp_pos q) (show Real.exp q ≤ Real.exp q+3 by linarith)
    simpa only [Real.log_exp] using h
  have hbase : 1 ≤ 1+Real.log (Real.exp q+3) := by linarith
  have hpow := le_self_pow₀ hbase (by norm_num : (9:ℕ) ≠ 0)
  unfold perronScaleWidth zetaContourWidth
  rw [div_div]
  apply div_le_div_of_nonneg_left hA (mul_pos (by norm_num) hq0)
  nlinarith

end JointDickman

end OAI
