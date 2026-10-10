import OAI.Analysis.LipschitzHilbert.Estimates.PolynomialEnvelope
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! The weighted Cauchy–Schwarz step in the local coefficient estimate. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert

theorem weighted_lintegral_cauchySchwarz {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (w f : Ω → ℝ) (hw : Measurable w) (hf : Measurable f)
    (hpos : ∀ x, 0 < w x) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal ((w x)⁻¹ ^ 2) ∂μ) ^ (1/2 : ℝ) *
      (∫⁻ x, ENNReal.ofReal ((w x)^2 * (f x)^2) ∂μ) ^ (1/2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (show (2:ℝ).HolderConjugate 2 from by norm_num [Real.holderConjugate_iff])
    (f := fun x => ENNReal.ofReal ((w x)⁻¹))
    (g := fun x => ENNReal.ofReal (w x * f x))
    (hw.inv.ennreal_ofReal.aemeasurable) ((hw.mul hf).ennreal_ofReal.aemeasurable)
  have heq (x : Ω) : ENNReal.ofReal ((w x)⁻¹) * ENNReal.ofReal (w x * f x) =
      ENNReal.ofReal (f x) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (hpos x).le), ← mul_assoc,
      inv_mul_cancel₀ (hpos x).ne', one_mul]
  have hs (x : Ω) : ENNReal.ofReal (w x * f x) ^ (2:ℝ) ≤
      ENNReal.ofReal ((w x)^2 * (f x)^2) := by
    rw [ENNReal.rpow_two]
    by_cases hx : 0 ≤ f x
    · rw [← ENNReal.ofReal_pow (mul_nonneg (hpos x).le hx), mul_pow]
    · rw [ENNReal.ofReal_eq_zero.mpr (mul_nonpos_of_nonneg_of_nonpos (hpos x).le (le_of_not_ge hx)), zero_pow (by decide)]
      exact bot_le
  simpa only [Pi.mul_apply, heq, ENNReal.rpow_two,
    ← ENNReal.ofReal_pow (inv_nonneg.mpr (hpos _).le)] using
    h.trans (mul_le_mul_right (ENNReal.rpow_le_rpow (lintegral_mono hs) (by norm_num)) _)

def referenceWeight (a b r W : ℝ) (z : ℝ × ℝ) : ℝ :=
  polynomialWeight a r 1 z.2 * polynomialWeight b W 1 z.1

theorem referenceWeight_pos (a b r W : ℝ) (z : ℝ × ℝ) :
    0 < referenceWeight a b r W z :=
  mul_pos (lt_of_lt_of_le zero_lt_one (polynomialWeight_one_le _ _ _ _))
    (lt_of_lt_of_le zero_lt_one (polynomialWeight_one_le _ _ _ _))

theorem referenceWeight_measurable (a b r W : ℝ) :
    Measurable (referenceWeight a b r W) := by
  unfold referenceWeight polynomialWeight
  fun_prop

theorem referenceWeight_inverse_integral (a b r W : ℝ) (hr : 0 < r) (hW : 0 < W) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal ((referenceWeight a b r W z)⁻¹ ^ 2)) ≤
      ENNReal.ofReal (Real.pi^2 * r * W) := by
  have hpoint (z : ℝ × ℝ) : (referenceWeight a b r W z)⁻¹ ^ 2 ≤
      lineEnvelope b W 1 z.1 * lineEnvelope a r 1 z.2 := by
    have hx := lineEnvelope_antitone a r z.2 (by decide : 1 ≤ 2)
    have hy := lineEnvelope_antitone b W z.1 (by decide : 1 ≤ 2)
    have heq : (referenceWeight a b r W z)⁻¹ ^ 2 =
        lineEnvelope b W 2 z.1 * lineEnvelope a r 2 z.2 := by
      simp only [referenceWeight, polynomialWeight, pow_one, mul_inv_rev, mul_pow,
        lineEnvelope, ← div_pow, ← inv_pow]
    rw [heq]
    exact mul_le_mul hy hx (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  calc
    _ ≤ ∫⁻ z : ℝ × ℝ, ENNReal.ofReal
        (lineEnvelope b W 1 z.1 * lineEnvelope a r 1 z.2) :=
      lintegral_mono (fun z => ENNReal.ofReal_le_ofReal (hpoint z))
    _ = ENNReal.ofReal (Real.pi^2 * r * W) := by
      rw [Measure.volume_eq_prod, lintegral_prod _ (by apply Measurable.aemeasurable; unfold lineEnvelope; fun_prop)]
      simp_rw [ENNReal.ofReal_mul (lineEnvelope_nonneg _ _ _ _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [← ofReal_integral_eq_lintegral_ofReal (integrable_lineEnvelope_one a r hr)
        (Filter.Eventually.of_forall (lineEnvelope_nonneg a r 1)),
        integral_lineEnvelope_one a r hr,
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
        ← ofReal_integral_eq_lintegral_ofReal (integrable_lineEnvelope_one b W hW)
          (Filter.Eventually.of_forall (lineEnvelope_nonneg b W 1)),
        integral_lineEnvelope_one b W hW, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end LipschitzHilbert

end

end OAI
