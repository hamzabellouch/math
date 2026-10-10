import Mathlib

namespace OAI

namespace Erdos970

section

open Filter
open scoped Topology
namespace ErdosInverseBoxHeight

theorem bin_inflation_le_power {B C xi : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    (1+xi)^(C*Real.log B) ≤ B^C := by
  have hB0 : 0 < B := by linarith
  have hx0 : 0 < 1+xi := by linarith
  have hlB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hlx : Real.log (1+xi) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos hx0
    linarith
  rw [Real.rpow_def_of_pos hx0,Real.rpow_def_of_pos hB0]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hlx (mul_nonneg hC hlB)]

theorem uniform_bin_inflation (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ B xi : ℝ,
      1 ≤ B → B ≤ Real.log z → 0 ≤ xi → xi ≤ 1 →
      (1+xi)^(C*Real.log B) ≤ z^((1:ℝ)/10) := by
  have hlog := (isLittleO_log_rpow_rpow_atTop C (by norm_num : (0:ℝ)<1/10)).bound zero_lt_one
  filter_upwards [eventually_gt_atTop (1:ℝ),hlog] with z hz hpow
  refine ⟨hz,?_⟩
  intro B xi hB hBz hxi0 hxi1
  have hz0 : 0 ≤ z := by linarith
  have hL0 : 0 ≤ Real.log z := Real.log_nonneg hz.le
  have hbound : (Real.log z)^C ≤ z^((1:ℝ)/10) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hL0 C),
      abs_of_nonneg (Real.rpow_nonneg hz0 ((1:ℝ)/10)),one_mul] using hpow
  exact (bin_inflation_le_power hB hC hxi0 hxi1).trans
    ((Real.rpow_le_rpow (by linarith : 0 ≤ B) hBz hC).trans hbound)

noncomputable def sourceZ (z : ℝ) : ℝ := Real.exp (Real.log z/Real.log (Real.log z))

theorem sourceZ_le_small_power : ∀ᶠ z : ℝ in atTop,
    1 < z ∧ 0 < sourceZ z ∧ sourceZ z ≤ z^((1:ℝ)/100) := by
  have hlog := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 100
  filter_upwards [eventually_gt_atTop (1:ℝ),hlog] with z hz hL
  dsimp only [Function.comp_apply] at hL
  refine ⟨hz,Real.exp_pos _,?_⟩
  have hz0 : 0 < z := by linarith
  have hlog0 : 0 ≤ Real.log z := (Real.log_pos hz).le
  rw [sourceZ,Real.rpow_def_of_pos hz0]
  apply Real.exp_le_exp.mpr
  have h := div_le_div_of_nonneg_left hlog0 (by norm_num : (0:ℝ)<100) hL
  convert! h using 1
  ring

end ErdosInverseBoxHeight

end

end Erdos970

end OAI
