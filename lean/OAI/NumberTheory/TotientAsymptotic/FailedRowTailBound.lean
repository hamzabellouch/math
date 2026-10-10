import OAI.NumberTheory.TotientAsymptotic.FailedRowMass

namespace OAI

/-! Uniform absorption of the residual row tail beyond its effective threshold. -/
noncomputable section
namespace TotientAsymptotic

lemma logarithm_two_power_bound {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (Real.log 2)^(-1-δ) ≤ 4 := by
  have hl : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hh := Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ)<1/2) hl
    (show -1-δ ≤ 0 by linarith)
  have ht := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0:ℝ)<1/2)
    (by norm_num : (1/2:ℝ) ≤ 1) (show (-2:ℝ) ≤ -1-δ by linarith)
  have he : (1/2:ℝ)^(-2:ℝ)=4 := by norm_num
  exact hh.trans (ht.trans_eq he)

lemma row_tail_coefficient_bound {δ b : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsize : δ⁻¹ ≤ Real.exp (δ*b)) :
    4*(Real.log 2)^(-1-δ)*(1+δ⁻¹)*Real.exp (-δ*b) ≤ 32 := by
  have he : δ⁻¹ ≤ Real.exp (δ*b) := hsize
  have hi := inv_anti₀ (inv_pos.mpr hδ) he
  have hexp : Real.exp (-δ*b) ≤ δ := by
    simpa only [← Real.exp_neg,inv_inv,neg_mul] using hi
  have htail : (1+δ⁻¹)*Real.exp (-δ*b) ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 1+δ⁻¹ by positivity)
    have hid : (1+δ⁻¹)*δ=1+δ := by field_simp; ring
    rw [hid] at hh
    linarith only [hh,hδ1]
  have hp := logarithm_two_power_bound hδ.le hδ1
  have hh := mul_le_mul hp htail (by positivity) (by norm_num : (0:ℝ)≤4)
  nlinarith only [hh]

end TotientAsymptotic

end

end OAI
