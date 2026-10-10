import OAI.NumberTheory.Ostmann.ZeroDensity.WeightedRieszRectangle
import OAI.NumberTheory.Ostmann.ZeroDensity.RieszNegativeTail

namespace OAI

/-! # Both tails for a bounded vertical coefficient in the Riesz integral -/

namespace Ostmann

open Complex MeasureTheory Set

theorem inverse_square_tail_bound (f : ℝ → ℂ) (K T : ℝ) (hT : 0 < T)
    (hb : ∀ t > T, ‖f t‖ ≤ K / t ^ 2) :
    ‖∫ t in Ioi T, f t‖ ≤ K / T := by
  have hg : IntegrableOn (fun t : ℝ => K * t ^ (-(2 : ℝ))) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hT).const_mul K
  have hn : ‖∫ t in Ioi T, f t‖ ≤ ∫ t in Ioi T, K * t ^ (-(2 : ℝ)) := by
    apply norm_integral_le_of_norm_le hg
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp : 0 < t := hT.trans ht
    simpa only [Real.rpow_neg hp.le, Real.rpow_two, div_eq_mul_inv] using hb t ht
  apply hn.trans_eq
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : -(2 : ℝ) < -1) hT]
  norm_num only [neg_add_cancel_left, neg_div_neg_eq, div_one, Real.rpow_neg_one]
  ring

theorem weightedRiesz_integrable (f : ℂ → ℂ) (X b M : ℝ) (hX : 0 < X) (hb : 1 ≤ b)
    (hc : Continuous (fun t : ℝ => f (rieszMellinLine b t)))
    (hbound : ∀ t : ℝ, ‖f (rieszMellinLine b t)‖ ≤ M) :
    Integrable (fun t => f (rieszMellinLine b t) * rieszVerticalWeight X b t) := by
  apply ((rieszVerticalWeight_integrable X b hX hb).norm.const_mul M).mono'
    ((hc.mul (rieszVerticalWeight_continuous X b hX (by linarith))).aestronglyMeasurable)
  filter_upwards with t
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _)

theorem weightedRiesz_both_tails (f : ℂ → ℂ) (X b M T : ℝ)
    (hX : 0 < X) (hM : 0 ≤ M) (hT : 0 < T)
    (hbound : ∀ t : ℝ, ‖f (rieszMellinLine b t)‖ ≤ M) :
    ‖∫ t in Ioi T, f (rieszMellinLine b t) * rieszVerticalWeight X b t‖ ≤ M * X ^ b / T ∧
    ‖∫ t in Iic (-T), f (rieszMellinLine b t) * rieszVerticalWeight X b t‖ ≤ M * X ^ b / T := by
  have hpoint (t : ℝ) (ht : t ≠ 0) :
      ‖f (rieszMellinLine b t) * rieszVerticalWeight X b t‖ ≤ M * X ^ b / t ^ 2 := by
    have hi : 0 < |(rieszMellinLine b t).im| := by
      simpa [rieszMellinLine] using abs_pos.mpr ht
    have hk := rieszMellinKernel_im_bound (rieszMellinLine b t) hi
    simp only [rieszMellinLine, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
      zero_add, sq_abs] at hk
    rw [norm_mul, rieszVerticalWeight_norm X b t hX]
    calc
      _ ≤ M * (X ^ b * (1 / t ^ 2)) :=
        mul_le_mul (hbound t) (mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg hX.le _))
          (by positivity) hM
      _ = _ := by ring
  constructor
  · exact inverse_square_tail_bound _ (M * X ^ b) T hT
      (fun t ht => hpoint t (ne_of_gt (hT.trans ht)))
  · rw [← integral_comp_neg_Ioi T (fun t => f (rieszMellinLine b t) * rieszVerticalWeight X b t)]
    apply inverse_square_tail_bound _ (M * X ^ b) T hT
    intro t ht
    simpa only [neg_sq] using hpoint (-t) (neg_ne_zero.mpr (ne_of_gt (hT.trans ht)))

end Ostmann

end OAI
