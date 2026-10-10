import OAI.NumberTheory.DirichletL.Hecke.DetectorFinite

namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorBudget
open HeckeDetectorPartition

lemma source_length_bound (U : ℝ) (hU : 2 ≤ U) :
    ((length (⌈2*U^21⌉₊ : ℝ)+1 : ℕ) : ℝ) ≤ 25*Real.logb 2 U := by
  have hUp : 0 < U := by linarith
  have hp : 1 ≤ U^21 := one_le_pow₀ (by linarith) (n := 21)
  have hc : (1 : ℝ) ≤ ⌈2*U^21⌉₊ := le_trans (by linarith) (Nat.le_ceil (2*U^21))
  have hcu : (⌈2*U^21⌉₊ : ℝ) ≤ 4*U^21 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 2*U^21 by positivity)
    linarith
  have hl : 1 ≤ Real.logb 2 U := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2) (by norm_num : (0 : ℝ)<2) hU
    simpa using h
  have hb := length_bound (⌈2*U^21⌉₊ : ℝ) hc
  have hm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2) (by linarith : (0 : ℝ)<⌈2*U^21⌉₊) hcu
  have he : Real.logb 2 (4*U^21) = 2+21*Real.logb 2 U := by
    rw [Real.logb_mul (by norm_num) (by positivity),Real.logb_pow]
    have hfour : Real.logb 2 4 = 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num,Real.logb_pow]
      norm_num
    rw [hfour]
    norm_num
  rw [he] at hm
  push_cast
  linarith

lemma source_pair_count_bound (U : ℝ) (hU : 2 ≤ U) :
    (((length (⌈2*U^21⌉₊ : ℝ)+1 : ℕ) : ℝ)^2) ≤ 625*(Real.logb 2 U)^2 := by
  have h := source_length_bound U hU
  have hl : 0 ≤ Real.logb 2 U := Real.logb_nonneg (by norm_num) (by linarith)
  nlinarith [sq_nonneg (((length (⌈2*U^21⌉₊ : ℝ)+1 : ℕ) : ℝ)-25*Real.logb 2 U)]

end SevenEighths.HeckeDetectorBudget

end

end OAI
