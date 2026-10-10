import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace OAI

/-! # Quadratic cancellation in the squarefree Euler logarithm -/
namespace JointDickman

noncomputable def squarefreeEulerLog (z : ℝ) (w : ℂ) : ℂ :=
  Complex.log (1+(z:ℂ)*w)+(z:ℂ)*Complex.log (1-w)

 theorem complex_log_error_bound {v : ℂ} {r : ℝ} (hr : r < 1) (hv : ‖v‖ ≤ r) :
    ‖Complex.log (1+v)-v‖ ≤ ‖v‖^2/(1-r) := by
  have hv1 : ‖v‖ < 1 := hv.trans_lt hr
  have hinv : (1-‖v‖)⁻¹ ≤ (1-r)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  calc
    _ ≤ ‖v‖^2*(1-‖v‖)⁻¹/2 := Complex.norm_log_one_add_sub_self_le hv1
    _ ≤ ‖v‖^2*(1-‖v‖)⁻¹ := div_le_self (by positivity) (by norm_num)
    _ ≤ ‖v‖^2*(1-r)⁻¹ := mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
    _ = _ := rfl

 theorem squarefreeEulerLog_norm_bound {z r : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hr : r < 1) {w : ℂ} (hw : ‖w‖ ≤ r) :
    ‖squarefreeEulerLog z w‖ ≤ 2*‖w‖^2/(1-r) := by
  have hzw : ‖(z:ℂ)*w‖ ≤ ‖w‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz]
    exact mul_le_of_le_one_left (norm_nonneg _) hz1
  have hv := complex_log_error_bound hr (hzw.trans hw)
  have hm := complex_log_error_bound hr (show ‖-w‖ ≤ r by simpa only [norm_neg] using hw)
  have heq : squarefreeEulerLog z w = (Complex.log (1+(z:ℂ)*w)-(z:ℂ)*w)+
      (z:ℂ)*(Complex.log (1-w)+w) := by unfold squarefreeEulerLog; ring
  rw [heq]
  have hq : 0 ≤ ‖w‖^2/(1-r) := by positivity
  calc
    _ ≤ ‖Complex.log (1+(z:ℂ)*w)-(z:ℂ)*w‖+
        ‖(z:ℂ)*(Complex.log (1-w)+w)‖ := norm_add_le _ _
    _ ≤ ‖w‖^2/(1-r)+‖w‖^2/(1-r) := by
      apply add_le_add
      · exact hv.trans (div_le_div_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hzw) (by linarith))
      · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz]
        have hm' : ‖Complex.log (1-w)+w‖ ≤ ‖w‖^2/(1-r) := by
          simpa only [norm_neg,sub_neg_eq_add,← sub_eq_add_neg] using hm
        exact (mul_le_mul_of_nonneg_left hm' hz).trans (mul_le_of_le_one_left hq hz1)
    _ = _ := by ring

 theorem squarefreeEulerLog_zero (z : ℝ) : squarefreeEulerLog z 0 = 0 := by
  simp [squarefreeEulerLog]

 theorem squarefreeEulerLog_exp {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {w : ℂ} (hw : ‖w‖ < 1) :
    Complex.exp (squarefreeEulerLog z w) = (1+(z:ℂ)*w)*Complex.exp ((z:ℂ)*Complex.log (1-w)) := by
  have hzw : ‖(z:ℂ)*w‖ < 1 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz]
    exact (mul_le_of_le_one_left (norm_nonneg _) hz1).trans_lt hw
  have hn : 1+(z:ℂ)*w ≠ 0 := by
    intro he
    have hv : (z:ℂ)*w = -1 := by linear_combination he
    rw [hv,norm_neg,norm_one] at hzw
    exact (lt_irrefl _ hzw)
  rw [squarefreeEulerLog,Complex.exp_add,Complex.exp_log hn]

end JointDickman

end OAI
