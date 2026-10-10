import Mathlib

namespace OAI

namespace Erdos970

section

open Filter
open scoped Topology
namespace ErdosSourcePolynomial

theorem eventual_value_budget_small (alpha delta : ℝ) (ha : 0 < alpha) (hd : 0 < delta) :
    ∀ᶠ z : ℝ in atTop, 2 ≤ z ∧ 1 ≤ Real.log z ∧ ∀ R : ℝ, z^alpha ≤ R →
      4*Real.log z+Real.log 4+8*R/(Real.log z)^4+3*R/Real.log z < delta*R := by
  have hlo := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) ha).bound (by positivity : 0 < delta/16)
  have hlarge := Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (44/delta))
  have hpow := (tendsto_rpow_atTop ha).eventually_ge_atTop (4*Real.log 4/delta)
  filter_upwards [hlo,hlarge,hpow,eventually_ge_atTop (2 : ℝ)] with z hsmall hL hP hz
  have hL1 : 1 ≤ Real.log z := (le_max_left _ _).trans hL
  have hL0 : 0 < Real.log z := by linarith
  have hz0 : 0 < z := by linarith
  have hpow0 : 0 < z^alpha := Real.rpow_pos_of_pos hz0 _
  have hlog : Real.log z ≤ delta/16*z^alpha := by
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_pos hL0,abs_of_pos hpow0] using hsmall
  have hconst : Real.log 4 ≤ delta/4*z^alpha := by
    have h := (div_le_iff₀ hd).mp hP
    nlinarith only [h]
  have h44 : 44/delta ≤ Real.log z := (le_max_right _ _).trans hL
  have hfrac : 11/Real.log z ≤ delta/4 := by
    apply (div_le_iff₀ hL0).mpr
    have h := (div_le_iff₀ hd).mp h44
    nlinarith only [h]
  have hLpow : Real.log z ≤ (Real.log z)^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : (1 : ℕ) ≤ 4)
  have h8 : 8/(Real.log z)^4 ≤ 8/Real.log z :=
    div_le_div_of_nonneg_left (by norm_num) hL0 hLpow
  have hsum : 8/(Real.log z)^4+3/Real.log z ≤ delta/4 := by
    calc
      _ ≤ 8/Real.log z+3/Real.log z := add_le_add h8 le_rfl
      _ = 11/Real.log z := by ring
      _ ≤ _ := hfrac
  refine ⟨hz,hL1,?_⟩
  intro R hR
  have hR0 : 0 < R := hpow0.trans_le hR
  have haR : 4*Real.log z ≤ delta/4*R := by
    have h := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ delta/4)
    nlinarith only [h,hlog]
  have hbR : Real.log 4 ≤ delta/4*R := hconst.trans (mul_le_mul_of_nonneg_left hR (by positivity))
  have hcR : 8*R/(Real.log z)^4+3*R/Real.log z ≤ delta/4*R := by
    convert! mul_le_mul_of_nonneg_right hsum hR0.le using 1
    ring
  nlinarith [mul_pos hd hR0]

end ErdosSourcePolynomial

end

end Erdos970

end OAI
