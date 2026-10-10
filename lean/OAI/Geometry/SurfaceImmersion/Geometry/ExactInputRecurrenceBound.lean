import OAI.Geometry.SurfaceImmersion.Correction.CorrectionScaleAlgebra

namespace OAI

/-! The two components of the actual input share a contracting affine bound. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection

theorem exact_input_recurrence_bound {t P P₀ Pm B C L B₀ : ℝ} {k : ℕ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hk : 10 ≤ k)
    (hPm : 0 ≤ Pm) (hB : 0 ≤ B) (hC : 0 ≤ C) (hL : 0 ≤ L) (hB₀ : 0 ≤ B₀) :
    P+P₀+t^(6/5 : ℝ)*Pm+(t^(6/5 : ℝ)/t)*C+
      (B*(t^(k : ℝ)*t^(6/5 : ℝ)))/(t^(6/5 : ℝ))^2+
      L*(1+B₀+C)*t^(1/5 : ℝ) ≤
    P+P₀+(Pm+B+L*(1+B₀)+1+L)*t^(1/5 : ℝ)*(1+C) := by
  have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
  have hτ : t^(6/5 : ℝ) ≤ t^(1/5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num)
  have hratio : t^(6/5 : ℝ)/t = t^(1/5 : ℝ) := by
    conv_lhs => rhs; rw [← Real.rpow_one t]
    rw [← Real.rpow_sub ht]
    norm_num
  have hquotient : (t^(k : ℝ)*t^(6/5 : ℝ))/(t^(6/5 : ℝ))^2 =
      t^((k : ℝ)-(6/5 : ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul ht.le,scale_quotient_product ht]
    congr 1
    ring
  have hquotient_le : (t^(k : ℝ)*t^(6/5 : ℝ))/(t^(6/5 : ℝ))^2 ≤ t^(1/5 : ℝ) := by
    rw [hquotient]
    exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  have hterm : (B*(t^(k : ℝ)*t^(6/5 : ℝ)))/(t^(6/5 : ℝ))^2 ≤ B*t^(1/5 : ℝ) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hquotient_le hB
  calc
    _ ≤ P+P₀+t^(1/5 : ℝ)*Pm+t^(1/5 : ℝ)*C+B*t^(1/5 : ℝ)+
        L*(1+B₀+C)*t^(1/5 : ℝ) := by
      rw [hratio]
      gcongr
    _ = P+P₀+(Pm+C+B+L*(1+B₀+C))*t^(1/5 : ℝ) := by ring
    _ ≤ _ := by
      apply add_le_add le_rfl
      rw [mul_assoc _ _ (1+C),mul_comm (t^(1/5 : ℝ)) (1+C),← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
      nlinarith [mul_nonneg hPm hC,mul_nonneg hB hC,
        mul_nonneg (mul_nonneg hL hB₀) hC]

end ClosedSurfaceR4.ExactCorrection

end

end OAI
