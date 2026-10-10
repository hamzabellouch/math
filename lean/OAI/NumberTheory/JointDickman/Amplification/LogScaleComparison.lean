import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OAI

/-! # Uniform logarithmic bounds on a fixed multiplicative neighborhood -/
namespace JointDickman

theorem log_near_scale {x t : ℝ} (hx : 0 < x) (hlog : 2 ≤ Real.log x)
    (ht : t ∈ Set.Icc (x/2) (2*x)) :
    Real.log x/2 ≤ Real.log t ∧ Real.log t ≤ 2*Real.log x := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity : 0 < x/2) ht.1
  have h2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  constructor
  · have h := Real.log_le_log (by positivity : 0 < x/2) ht.1
    rw [Real.log_div hx.ne' (by norm_num : (2:ℝ) ≠ 0)] at h
    linarith
  · have h := Real.log_le_log ht0 ht.2
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hx.ne'] at h
    linarith

theorem rpow_comparable {u v β : ℝ} (hv : 0 < v)
    (hu : v/2 ≤ u ∧ u ≤ 2*v) :
    u^β ≤ (2:ℝ)^(|β|)*v^β := by
  by_cases hβ : 0 ≤ β
  · calc
      _ ≤ (2*v)^β := Real.rpow_le_rpow (by linarith) hu.2 hβ
      _ = _ := by rw [Real.mul_rpow (by norm_num) hv.le,abs_of_nonneg hβ]
  · have hβ' : β < 0 := lt_of_not_ge hβ
    calc
      _ ≤ (v/2)^β := Real.rpow_le_rpow_of_nonpos (by positivity) hu.1 hβ'.le
      _ = _ := by
        rw [Real.div_rpow hv.le (by norm_num),abs_of_neg hβ',Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
        ring

theorem log_rpow_near_scale (β : ℝ) {x t : ℝ} (hx : 0 < x) (hlog : 2 ≤ Real.log x)
    (ht : t ∈ Set.Icc (x/2) (2*x)) :
    (Real.log t)^β ≤ (2:ℝ)^(|β|)*(Real.log x)^β :=
  rpow_comparable (by linarith) (log_near_scale hx hlog ht)

end JointDickman

end OAI
