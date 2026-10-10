import OAI.NumberTheory.Ostmann.Conclusion.Scales
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalGoodNormalizerBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Conclusion

theorem diagonal_good_two_errors_le {A m : ℝ} (hA : 0 ≤ A) (hm : 1 ≤ m) (j : ℕ) :
    Real.exp (-(A+1)*m) + Real.exp (-(A+1)*(2:ℝ)^j*m)  ≤  Real.exp (-A*m) := by
  have hm0 : 0 ≤ m := le_trans zero_le_one hm
  have hp : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
  have hexp : Real.exp (-(A+1)*(2:ℝ)^j*m)  ≤  Real.exp (-(A+1)*m) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (by simpa only [mul_one] using mul_le_mul_of_nonpos_left hp (by linarith : -(A+1) ≤ 0)) hm0
  have he : (2:ℝ) ≤ Real.exp m := by
    have := Real.add_one_le_exp m
    linarith
  calc
    _  ≤  2*Real.exp (-(A+1)*m) := by linarith
    _  ≤  Real.exp m*Real.exp (-(A+1)*m) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = Real.exp (-A*m) := by rw [←Real.exp_add]; congr 1; ring

end Ostmann.Conclusion

end

end OAI
