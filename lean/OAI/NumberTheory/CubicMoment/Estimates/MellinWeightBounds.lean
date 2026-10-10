import OAI.NumberTheory.CubicMoment.Estimates.TruncatedMellin

namespace OAI

/-!
# The height weight in the truncated Mellin integral

The interval transform has the expected `1/(1+|ξ|)` bound, including
at frequency zero. The cutoff and the scaling phase have norm at most one.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace CubicFirstMoment

lemma norm_dyadicFourierMultiplier_le_log (ξ : ℝ) :
    ‖dyadicFourierMultiplier ξ‖ ≤ Real.log 2 := by
  unfold dyadicFourierMultiplier
  rw [fourier_intervalStep_eq_integral (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := Real.log 2) (C := (1 : ℝ))
    (f := fun x => Complex.exp ((-2*Real.pi*x*ξ : ℝ)*Complex.I))
    (fun x _ => (Complex.norm_exp_ofReal_mul_I _).le)
  simpa only [sub_zero, abs_of_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)),
    one_mul] using h

lemma norm_dyadicFourierMultiplier_nonzero {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖dyadicFourierMultiplier ξ‖ ≤ 2/(2*Real.pi*|ξ|) := by
  unfold dyadicFourierMultiplier
  rw [dyadic_interval_multiplier hξ, norm_div]
  have hn : ‖(1 : ℂ) - Complex.exp ((-2*Real.pi*Real.log 2*ξ : ℝ)*Complex.I)‖ ≤ 2 := by
    simpa only [norm_one, Complex.norm_exp_ofReal_mul_I, one_add_one_eq_two] using
      norm_sub_le (1 : ℂ) (Complex.exp ((-2*Real.pi*Real.log 2*ξ : ℝ)*Complex.I))
  have hd : ‖((2*Real.pi*ξ : ℝ) : ℂ)*Complex.I‖ = 2*Real.pi*|ξ| := by
    rw [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]
  rw [hd]
  exact div_le_div_of_nonneg_right hn (by positivity)

lemma norm_dyadicFourierMultiplier_le (ξ : ℝ) :
    ‖dyadicFourierMultiplier ξ‖ ≤ 2/(1+|ξ|) := by
  have hr : 0 ≤ |ξ| := abs_nonneg ξ
  have hd : 0 < 1+|ξ| := by positivity
  by_cases hsmall : |ξ| ≤ 1
  · have hlog : Real.log 2 ≤ 1 := by
      simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    exact (norm_dyadicFourierMultiplier_le_log ξ).trans
      (hlog.trans ((le_div_iff₀ hd).mpr (by linarith)))
  · have hr1 : 1 < |ξ| := lt_of_not_ge hsmall
    have hξ : ξ ≠ 0 := abs_pos.mp (by linarith)
    apply (norm_dyadicFourierMultiplier_nonzero hξ).trans
    apply div_le_div_of_nonneg_left (by norm_num) hd
    nlinarith [Real.pi_gt_three]

lemma norm_frequencyCutoff_le_one (ξ : ℝ) : ‖frequencyCutoff ξ‖ ≤ 1 := by
  rw [frequencyCutoff_apply,Complex.norm_real,Real.norm_of_nonneg frequencyBump.nonneg]
  exact frequencyBump.le_one

/-- The common weight in the actual arithmetic integral has exactly the
height decay needed for the later dyadic-height estimates. -/
theorem norm_truncatedMellinWeight_le (X T ξ : ℝ) :
    ‖truncatedMellinWeight X T ξ‖ ≤ 2/(1+|ξ|) := by
  rw [truncatedMellinWeight,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul,norm_mul]
  exact (mul_le_of_le_one_left (_root_.norm_nonneg _)
    (norm_frequencyCutoff_le_one _)).trans (norm_dyadicFourierMultiplier_le ξ)

end CubicFirstMoment

end

end OAI
