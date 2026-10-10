import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import OAI.NumberTheory.Ostmann.ZeroDensity.RieszTailEstimate

namespace OAI

/-! # The lower right-contour tail -/

namespace Ostmann

open Complex MeasureTheory Set

theorem rightRieszIntegrand_negative_tail : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (X σ T : ℝ), 0 < X → 1 < σ → σ ≤ 2 → 0 < T →
      ‖∫ t in Iic (-T), rightRieszIntegrand χ X σ t‖ ≤
        (1 / (σ - 1) + C) * X ^ σ / T := by
  obtain ⟨C, hC, hb⟩ := character_logDeriv_right_pole_bound
  refine ⟨C, hC, ?_⟩
  intro χ X σ T hX hσ hσ2 hT
  rw [← integral_comp_neg_Ioi T (rightRieszIntegrand χ X σ)]
  let K := (1 / (σ - 1) + C) * X ^ σ
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hg : IntegrableOn (fun t : ℝ => K * t ^ (-(2 : ℝ))) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hT).const_mul K
  have hn : ‖∫ t in Ioi T, rightRieszIntegrand χ X σ (-t)‖ ≤
      ∫ t in Ioi T, K * t ^ (-(2 : ℝ)) := by
    apply norm_integral_le_of_norm_le hg
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htp : 0 < t := hT.trans ht
    have hlog := hb χ (rieszMellinLine σ (-t)) (by simpa using hσ) (by simpa using hσ2)
    simp only [rieszMellinLine_re] at hlog
    have hkernel := rieszMellinKernel_im_bound (rieszMellinLine σ (-t)) (by simpa [rieszMellinLine, abs_neg, abs_of_pos htp] using htp)
    simp only [rieszMellinLine, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
      zero_add, abs_neg, abs_of_pos htp] at hkernel
    rw [rightRieszIntegrand, norm_mul, norm_neg, rieszVerticalWeight_norm X σ (-t) hX]
    calc
      _ ≤ (1 / (σ - 1) + C) * (X ^ σ * (1 / t ^ 2)) := by
        exact mul_le_mul hlog (mul_le_mul_of_nonneg_left hkernel (Real.rpow_nonneg hX.le _))
          (by positivity) (by positivity)
      _ = K * t ^ (-(2 : ℝ)) := by
        rw [Real.rpow_neg htp.le, Real.rpow_two]
        dsimp [K]
        ring
  apply hn.trans_eq
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : -(2 : ℝ) < -1) hT]
  norm_num only [neg_add_cancel_left, neg_div_neg_eq, div_one, Real.rpow_neg_one]
  dsimp [K]
  ring

end Ostmann

end OAI
