import OAI.NumberTheory.TotientAsymptotic.FordLargestPrime
import OAI.NumberTheory.TotientAsymptotic.CoordinateThreshold

namespace OAI

/-! A failed row with a sufficiently large leading prime is a relative row failure. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma large_head_log_budget {b ω : ℝ} (hb : 1 ≤ b) (hω : 0 < ω)
    (hsize : (8000/ω)^2 ≤ b) : 4*Real.log (1000*b) ≤ ω*b := by
  have hb0 : 0 ≤ b := by linarith
  have hr : 1 ≤ Real.sqrt b := (Real.le_sqrt (by norm_num) hb0).mpr (by simpa using hb)
  have hl := Real.log_le_rpow_div hb0 (by norm_num : (0:ℝ)<1/2)
  rw [← Real.sqrt_eq_rpow] at hl
  have hs : 8000/ω ≤ Real.sqrt b := (Real.le_sqrt (by positivity) hb0).mpr hsize
  have hw : 8000 ≤ ω*Real.sqrt b := by
    have hh := (div_le_iff₀ hω).mp hs
    linarith only [hh]
  have hm := mul_le_mul_of_nonneg_right hw (Real.sqrt_nonneg b)
  rw [mul_assoc,Real.mul_self_sqrt hb0] at hm
  rw [Real.log_mul (by norm_num : (1000:ℝ)≠0) (by linarith : b≠0)]
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1000)
  nlinarith only [hl,hr,hm,hc]

lemma large_head_coordinate {v n : ℕ} (hv : 1 < v) (hB : 0 < B (v:ℝ))
    (hhead : Real.exp (Real.log v/(1000*B v)) ≤ (largestPrimeFactor n:ℝ)) :
    B v-Real.log (1000*B v) ≤ fordPrimeCoordinate n 0 := by
  rw [← fordPrime_zero_eq_largest n] at hhead
  have hvR : (1:ℝ) < v := by exact_mod_cast hv
  have ht : 0 < Real.log v/(1000*B v) := div_pos (Real.log_pos hvR) (by positivity)
  have hp : (0:ℝ) < fordPrime n 0 := (Real.exp_pos _).trans_le hhead
  have hl : Real.log v/(1000*B v) ≤ Real.log (fordPrime n 0) :=
    (Real.le_log_iff_exp_le hp).mpr hhead
  have hh := Real.log_le_log ht hl
  rw [Real.log_div (Real.log_pos hvR).ne' (by positivity : 1000*B (v:ℝ)≠0)] at hh
  exact hh.trans (le_max_right _ _)

lemma large_head_row_relative {v n k : ℕ} {ω : ℝ}
    (hv : 1 < v) (hB : 1 ≤ B (v:ℝ)) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hsize : (8000/ω)^2 ≤ B (v:ℝ))
    (hhead : Real.exp (Real.log v/(1000*B v)) ≤ (largestPrimeFactor n:ℝ))
    (hrow : (1+ω)*fordPrimeCoordinate n 0 <
      ∑ i : Fin k,a (i.val+1)*fordPrimeCoordinate n (i.val+1)) :
    (1+ω/2)*B v < ∑ i : Fin k,a (i.val+1)*fordPrimeCoordinate n (i.val+1) := by
  have hh := large_head_coordinate hv (by linarith) hhead
  have hbudget := large_head_log_budget hB hω hsize
  have hl : 0 ≤ Real.log (1000*B (v:ℝ)) := Real.log_nonneg (by linarith only [hB])
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 1+ω by linarith)
  have he := mul_le_mul_of_nonneg_right hω1 hl
  nlinarith only [hm,he,hbudget,hrow]

end TotientAsymptotic

end

end OAI
