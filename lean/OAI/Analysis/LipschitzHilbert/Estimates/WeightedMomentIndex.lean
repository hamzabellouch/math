import OAI.Analysis.LipschitzHilbert.Estimates.WeightedExceptionalArea
import Mathlib.Algebra.Order.Floor.Ring

namespace OAI

/-! A spatially varying natural moment order turns uniform local
exponential tails into a summable global exceptional set. -/

noncomputable section
open scoped ENNReal
namespace LipschitzHilbert

def weightedMomentIndex (n : ℕ) (w : ℝ) : ℕ := n + ⌈w⁻¹⌉₊

theorem quarter_pow_ceil_inv_le (w : ℝ) (hw : 0 < w) :
    (1/4:ℝ)^(⌈w⁻¹⌉₊) ≤ w := by
  have hceil : w⁻¹ ≤ (⌈w⁻¹⌉₊:ℝ) := Nat.le_ceil _
  have hpow : (⌈w⁻¹⌉₊:ℝ) ≤ (4:ℝ)^⌈w⁻¹⌉₊ := by
    have hb := one_add_mul_le_pow (by norm_num : (-2:ℝ) ≤ 3) ⌈w⁻¹⌉₊
    norm_num at hb
    nlinarith [inv_pos.mpr hw]
  rw [div_pow, one_pow]
  apply (div_le_iff₀ (by positivity : 0 < (4:ℝ)^⌈w⁻¹⌉₊)).mpr
  have h := mul_le_mul_of_nonneg_left (hceil.trans hpow) hw.le
  simpa only [mul_inv_cancel₀ hw.ne'] using h

theorem weightedMomentIndex_pos (n : ℕ) (hn : 1 ≤ n) (w : ℝ) :
    1 ≤ weightedMomentIndex n w := hn.trans (Nat.le_add_right _ _)

theorem weightedMomentIndex_le (n : ℕ) (hn : 1 ≤ n) (w : ℝ)
    (hw : 0 < w) (hw1 : w ≤ 1) :
    (weightedMomentIndex n w : ℝ) ≤ 3*(n:ℝ)/w := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hceil : (⌈w⁻¹⌉₊:ℝ) ≤ w⁻¹+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hm := mul_le_mul_of_nonneg_right hceil hw.le
  rw [add_mul, inv_mul_cancel₀ hw.ne', one_mul] at hm
  have hnw := mul_le_mul_of_nonneg_left hw1 (Nat.cast_nonneg n)
  apply (le_div_iff₀ hw).mpr
  simp only [weightedMomentIndex, Nat.cast_add]
  nlinarith

theorem weightedMomentIndex_tail (n : ℕ) (w : ℝ) (hw : 0 < w) :
    (1/4:ℝ≥0∞)^(weightedMomentIndex n w) ≤
      (1/4:ℝ≥0∞)^n*ENNReal.ofReal w := by
  have h := ENNReal.ofReal_le_ofReal (quarter_pow_ceil_inv_le w hw)
  have heq : ENNReal.ofReal ((1/4:ℝ)^⌈w⁻¹⌉₊) = (1/4:ℝ≥0∞)^⌈w⁻¹⌉₊ := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [heq] at h
  simpa only [weightedMomentIndex, pow_add] using mul_le_mul' (le_refl ((1/4:ℝ≥0∞)^n)) h

end LipschitzHilbert

end

end OAI
