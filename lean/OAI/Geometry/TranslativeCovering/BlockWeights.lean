import OAI.Geometry.TranslativeCovering.RowGrouping

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace BlockWeights

lemma bin_parameters {w q s ell ell' C c D k : ℝ}
    (hC : 1 ≤ C) (hc : 0 < c) (hq : 0 ≤ q) (hk : 0 ≤ k)
    (hl : ell ≤ q) (hl' : ell' ≤ s)
    (htrivial : w ≤ Real.exp (-|q-s|/2))
    (haff : w ≤ C*Real.exp ((ell+ell')/2-c*D))
    (hbin : Real.exp (-(k+1)) < w) :
    s < q+2*(k+1) ∧ ell' < 2*(q+k+1) ∧
      D ≤ ((Real.log C+2)/c)*(q+k+1) := by
  have hpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hb := Real.exp_lt_exp.mp (hbin.trans_le htrivial)
  have habs := neg_le_abs (q-s)
  have hs : s < q+2*(k+1) := by linarith
  refine ⟨hs, by linarith, ?_⟩
  have he : C*Real.exp ((ell+ell')/2-c*D) =
      Real.exp (Real.log C+(ell+ell')/2-c*D) := by
    rw [show Real.log C+(ell+ell')/2-c*D =
      Real.log C+((ell+ell')/2-c*D) by ring, Real.exp_add, Real.exp_log hpos]
  rw [he] at haff
  have hdist := Real.exp_lt_exp.mp (hbin.trans_le haff)
  have hlog := Real.log_nonneg hC
  have hmul := mul_nonneg hlog (by linarith : 0 ≤ q+k)
  have hD : c*D ≤ (Real.log C+2)*(q+k+1) := by nlinarith
  calc
    D ≤ (Real.log C+2)*(q+k+1)/c := (le_div_iff₀ hc).mpr (by nlinarith)
    _ = _ := by ring

lemma binary_above_exp (k : ℕ) : Real.exp (-((k:ℝ)+1)) ≤ (1/2:ℝ)^(k+1) := by
  have he : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); norm_num at this ⊢; exact this
  have hhalf : Real.exp (-1) ≤ (1/2:ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using (inv_le_inv₀ (Real.exp_pos _) (by norm_num : (0:ℝ)<2)).mpr he
  have hp := pow_le_pow_left₀ (Real.exp_pos (-1)).le hhalf (k+1)
  rw [← Real.exp_nat_mul] at hp
  simpa only [Nat.cast_add, Nat.cast_one, mul_neg, mul_one] using hp

end BlockWeights

end OAI
