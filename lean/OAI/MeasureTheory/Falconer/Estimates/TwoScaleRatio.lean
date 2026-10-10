import OAI.MeasureTheory.Falconer.Incidence.InterpolatedIncidence

namespace OAI

/-! The numerical compatibility of the normalized local factor and the
large-pencil improvement. A large coarse union forces a fine-scale gain. -/
namespace Falconer

theorem two_scale_ratio_bound {x a C F β : ℝ}
    (hx : 0 < x) (ha : 0 ≤ a) (hC : 0 ≤ C) (hF : 1 ≤ F)
    (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hcoarse : x^2 ≤ C*a*x^(1-β)) (hlocal : a ≤ F*x) :
    a^β ≤ C*F^2 := by
  have hF0 : 0 ≤ F := zero_le_one.trans hF
  have hfac : 0 < x*x^(1-β) := mul_pos hx (Real.rpow_pos_of_pos hx _)
  have hxeq : x^β*(x*x^(1-β)) = x^2 := by
    rw [mul_left_comm,← Real.rpow_add hx]
    norm_num
    ring
  have hxp : x^β ≤ C*F := by
    apply (mul_le_mul_iff_left₀ hfac).1
    calc
      x^β*(x*x^(1-β)) = x^2 := hxeq
      _ ≤ C*a*x^(1-β) := hcoarse
      _ ≤ C*(F*x)*x^(1-β) := by gcongr
      _ = (C*F)*(x*x^(1-β)) := by ring
  have hFp : F^β ≤ F := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hF hβ1
  calc
    a^β ≤ (F*x)^β := Real.rpow_le_rpow ha hlocal hβ.le
    _ = F^β*x^β := Real.mul_rpow hF0 hx.le
    _ ≤ F*(C*F) := mul_le_mul hFp hxp (Real.rpow_nonneg hx.le _) hF0
    _ = C*F^2 := by ring

theorem normalize_interpolated_incidence {ρ s m B K L A H β : ℝ}
    (hρ : 0 < ρ) (hB : 0 < B) (hm : 0 < m) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hraw : (m/B)^2 ≤ A*
      (((K*(80*ρ)^s*(L*m))^(1-β)*(25921:ℝ)^β)*H)) :
    (m*ρ^s)^2 ≤
      (B^2*(L*K*80^s)^(1-β)*(25921:ℝ)^β*H)*(A*(ρ^s)^2)*(m*ρ^s)^(1-β) := by
  have hr : 0 < ρ^s := Real.rpow_pos_of_pos hρ _
  have hbase : K*(80*ρ)^s*(L*m) = (L*K*80^s)*(m*ρ^s) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 80) hρ.le]
    ring
  rw [hbase,Real.mul_rpow (by positivity : 0 ≤ L*K*80^s) (mul_pos hm hr).le] at hraw
  have hh := mul_le_mul_of_nonneg_right hraw (sq_nonneg (B*ρ^s))
  convert hh using 1 <;> field_simp

end Falconer

end OAI
