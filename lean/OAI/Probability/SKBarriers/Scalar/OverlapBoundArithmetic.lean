import Mathlib

namespace OAI

section

section
noncomputable section
namespace SK.Analytic

theorem overlap_error_arithmetic {k v : ℝ} (hk : 1 ≤ k) (hv : 0 < v)
    (hkv : k/Real.sqrt v ≤ 1) :
    let E := 1/(k+1)+2*(k+1)/v
    k*Real.sqrt (2/v)+3*Real.sqrt k/(k+1)+E+2*Real.sqrt E+4/(k+1) ≤
      20*(k/Real.sqrt v+1/Real.sqrt k) := by
  have hk0 : 0 < k := by linarith
  have hrk : 0 < Real.sqrt k := Real.sqrt_pos.2 hk0
  have hrv : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have hksq : k^2 ≤ v := by
    have hh := (div_le_one hrv).1 hkv
    nlinarith [Real.sq_sqrt hv.le]
  have hroot : Real.sqrt k ≤ k := by
    nlinarith [Real.sq_sqrt hk0.le]
  have hK : 0 < k+1 := by linarith
  have hE : 1/(k+1)+2*(k+1)/v ≤ 5/k := by
    have h1 := one_div_le_one_div_of_le hk0 (show k ≤ k+1 by linarith)
    have h2 : 2*(k+1)/v ≤ 4/k := by
      calc
        _ ≤ 2*(2*k)/(k^2) := div_le_div₀ (by positivity) (by nlinarith) (sq_pos_of_pos hk0) hksq
        _ = _ := by field_simp; ring
    calc
      _ ≤ 1/k+4/k := add_le_add h1 h2
      _ = _ := by ring
  have hEsqrt : Real.sqrt (1/(k+1)+2*(k+1)/v) ≤ 3/Real.sqrt k := by
    calc
      _ ≤ Real.sqrt (9/k) := Real.sqrt_le_sqrt (hE.trans (div_le_div_of_nonneg_right (by norm_num) hk0.le))
      _ = _ := by rw [Real.sqrt_div (by norm_num)]; norm_num
  have hfirst : k*Real.sqrt (2/v) ≤ 2*(k/Real.sqrt v) := by
    rw [Real.sqrt_div (by norm_num)]
    have htwo : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2 : ℝ)]
    have H := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right htwo hrv.le) hk0.le
    calc
      _ ≤ k*(2/Real.sqrt v) := H
      _ = _ := by ring
  have hmean : 3*Real.sqrt k/(k+1) ≤ 3/Real.sqrt k := by
    apply (div_le_div_iff₀ hK hrk).2
    nlinarith [Real.sq_sqrt hk0.le]
  have hEfinal : 1/(k+1)+2*(k+1)/v ≤ 5/Real.sqrt k :=
    hE.trans (div_le_div_of_nonneg_left (by norm_num) hrk hroot)
  have hlast : 4/(k+1) ≤ 4/Real.sqrt k :=
    div_le_div_of_nonneg_left (by norm_num) hrk (hroot.trans (by linarith))
  dsimp only
  have ha : 0 ≤ k/Real.sqrt v := by positivity
  have hb : 0 ≤ 1/Real.sqrt k := by positivity
  simp only [div_eq_mul_inv] at hEsqrt hfirst hmean hEfinal hlast ha hb ⊢
  linarith
end SK.Analytic

end
end

end

end OAI
