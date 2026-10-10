import OAI.NumberTheory.CubicMoment.Estimates.WeightedPrimeInput

namespace OAI

/-! The inverse logarithm weight used to remove von Mangoldt's prime
logarithm. Its endpoint and total-variation cost is explicit. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def inverseLogWeight (t : ℝ) : ℂ := ((Real.log t)⁻¹:ℝ)
def inverseLogDerivative (t : ℝ) : ℝ := -t⁻¹/(Real.log t)^2

lemma inverseLog_hasDerivAt {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun x : ℝ => (Real.log x)⁻¹) (inverseLogDerivative t) t :=
  (Real.hasDerivAt_log (by linarith : t ≠ 0)).inv (Real.log_pos ht).ne'

lemma inverseLogWeight_hasDerivAt {t : ℝ} (ht : 1 < t) :
    HasDerivAt inverseLogWeight (inverseLogDerivative t:ℂ) t :=
  (inverseLog_hasDerivAt ht).ofReal_comp

lemma inverseLogDerivative_continuousOn {a b : ℝ} (ha : 1 < a) :
    ContinuousOn inverseLogDerivative (Icc a b) := by
  intro t ht
  have ht1 : 1 < t := ha.trans_le ht.1
  have ht0 : t ≠ 0 := by linarith
  exact ((continuousAt_inv₀ ht0).neg.div ((Real.continuousAt_log ht0).pow 2)
    (pow_ne_zero 2 (Real.log_pos ht1).ne')).continuousWithinAt

lemma inverseLogWeight_deriv_norm {t : ℝ} (ht : 1 < t) :
    ‖deriv inverseLogWeight t‖ = -inverseLogDerivative t := by
  rw [(inverseLogWeight_hasDerivAt ht).deriv,Complex.norm_real,Real.norm_eq_abs]
  apply abs_of_nonpos
  unfold inverseLogDerivative
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (inv_nonneg.mpr (by linarith))) (sq_nonneg _)

lemma inverseLogWeight_integrableOn_deriv {a b : ℝ} (ha : 1 < a) :
    IntegrableOn (deriv inverseLogWeight) (Icc a b) := by
  have hh : IntegrableOn (fun t : ℝ => (inverseLogDerivative t : ℂ)) (Icc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn
    (inverseLogDerivative_continuousOn (b := b) ha)).integrableOn_Icc
  apply hh.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (inverseLogWeight_hasDerivAt (ha.trans_le ht.1)).deriv.symm

lemma inverseLogWeight_variation {a b : ℝ} (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    ‖inverseLogWeight a‖+‖inverseLogWeight b‖+
      (∫ t in Ioc a b, ‖deriv inverseLogWeight t‖) ≤ 2 := by
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le ha
  have hb1 : 1 < b := ha1.trans_le hab
  have hcont := inverseLogDerivative_continuousOn (b := b) ha1
  have hint : IntervalIntegrable inverseLogDerivative volume a b :=
    hcont.intervalIntegrable_of_Icc hab
  have hft : (∫ t in a..b, inverseLogDerivative t) = (Real.log b)⁻¹-(Real.log a)⁻¹ := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hint
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact inverseLog_hasDerivAt (ha1.trans_le ht.1)
  have hn : (∫ t in Ioc a b, ‖deriv inverseLogWeight t‖) =
      (Real.log a)⁻¹-(Real.log b)⁻¹ := by
    calc
      _ = ∫ t in Ioc a b, -inverseLogDerivative t := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact inverseLogWeight_deriv_norm (ha1.trans ht.1)
      _ = -(∫ t in a..b, inverseLogDerivative t) := by
        rw [integral_neg,intervalIntegral.integral_of_le hab]
      _ = _ := by rw [hft]; ring
  have hla : 1 ≤ Real.log a := by
    have hh := Real.log_le_log (Real.exp_pos 1) ha
    simpa only [Real.log_exp] using hh
  have hia : (Real.log a)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hla
  rw [hn]
  simp only [inverseLogWeight,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.log_pos ha1).le),
    abs_of_nonneg (inv_nonneg.mpr (Real.log_pos hb1).le)]
  linarith

end CubicFirstMoment

end

end OAI
