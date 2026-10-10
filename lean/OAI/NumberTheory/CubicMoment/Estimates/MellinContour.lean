import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace OAI

/-! Contour shifting for the Mellin integrals in the smooth Hecke sum.
The horizontal edges are kept explicit until a uniform decay bound is
available; no functional equation or dual-sum estimate is assumed here. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace CubicFirstMoment

def closedVerticalStrip (a b : ℝ) : Set ℂ :=
  {z | a ≤ z.re ∧ z.re ≤ b}

lemma mellin_rectangle_identity {a b : ℝ} (hab : a ≤ b)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (closedVerticalStrip a b))
    (T : ℝ) :
    (∫ x in a..b, f (x - (T : ℂ) * Complex.I)) -
      (∫ x in a..b, f (x + (T : ℂ) * Complex.I)) +
      Complex.I * (∫ y in -T..T, f (b + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y in -T..T, f (a + (y : ℂ) * Complex.I)) = 0 := by
  have hd := hf.mono (show
      (Set.uIcc a b ×ℂ Set.uIcc (-T) T) ⊆ closedVerticalStrip a b from by
    intro z hz
    simpa only [Set.uIcc_of_le hab, Set.mem_preimage, Set.mem_Icc,
      closedVerticalStrip, Set.mem_ofPred_eq] using hz.1)
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a : ℂ) - (T : ℂ) * Complex.I) ((b : ℂ) + (T : ℂ) * Complex.I)
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.sub_im, Complex.add_im, mul_zero,
    sub_zero, add_zero, zero_sub, mul_one, zero_add] at h
  simpa only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.sub_im, Complex.add_im, mul_zero, zero_mul,
    sub_zero, add_zero, zero_sub, mul_one, zero_add, Complex.ofReal_neg,
    neg_mul, add_neg_cancel, sub_self, smul_eq_mul, sub_eq_add_neg] using h hd

/-- Vertical Mellin integrals agree after shifting through a holomorphic
strip, once both horizontal edges vanish. -/
theorem mellin_contour_shift {a b : ℝ} (hab : a ≤ b)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (closedVerticalStrip a b))
    (ha : Integrable (fun y : ℝ => f (a + (y : ℂ) * Complex.I)))
    (hb : Integrable (fun y : ℝ => f (b + (y : ℂ) * Complex.I)))
    (hTop : Tendsto (fun T : ℝ => ∫ x in a..b, f (x + (T : ℂ) * Complex.I))
      atTop (𝓝 0))
    (hBot : Tendsto (fun T : ℝ => ∫ x in a..b, f (x - (T : ℂ) * Complex.I))
      atTop (𝓝 0)) :
    (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) =
      ∫ y : ℝ, f (b + (y : ℂ) * Complex.I) := by
  have hia := intervalIntegral_tendsto_integral ha
    tendsto_neg_atTop_atBot tendsto_id
  have hib := intervalIntegral_tendsto_integral hb
    tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hBot.sub hTop).add (hib.const_mul Complex.I)).sub
    (hia.const_mul Complex.I)
  have hz : (0 : ℂ) + Complex.I * (∫ y : ℝ, f (b + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) = 0 := by
    have hz' : 0 - 0 + Complex.I * (∫ y : ℝ, f (b + (y : ℂ) * Complex.I)) -
        Complex.I * (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) = 0 := by
      apply tendsto_nhds_unique hlim
      apply tendsto_const_nhds.congr'
      exact Filter.Eventually.of_forall (fun T => (mellin_rectangle_identity hab f hf T).symm)
    simpa only [sub_self] using hz'
  have he : Complex.I * (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) =
      Complex.I * (∫ y : ℝ, f (b + (y : ℂ) * Complex.I)) := by
    linear_combination -hz
  exact mul_left_cancel₀ Complex.I_ne_zero he

/-- A common decaying majorant supplies both horizontal limits. This is
the form used for a rapidly decreasing Mellin transform times an
L-function of polynomial growth. -/
theorem mellin_contour_shift_of_majorant {a b : ℝ} (hab : a ≤ b)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (closedVerticalStrip a b))
    (H : ℝ → ℝ) (hH : Integrable H)
    (hHtop : Tendsto H atTop (𝓝 0)) (hHbot : Tendsto H atBot (𝓝 0))
    (hbound : ∀ x ∈ Icc a b, ∀ t : ℝ, ‖f (x + (t : ℂ) * Complex.I)‖ ≤ H t) :
    (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) =
      ∫ y : ℝ, f (b + (y : ℂ) * Complex.I) := by
  have hline (x : ℝ) (hx : x ∈ Icc a b) :
      Integrable (fun y : ℝ => f (x + (y : ℂ) * Complex.I)) := by
    have hc : Continuous (fun y : ℝ => f (x + (y : ℂ) * Complex.I)) :=
      hf.continuousOn.comp_continuous
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
        (by intro y; simpa [closedVerticalStrip] using hx)
    exact hH.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall (hbound x hx))
  have hedge (t : ℝ) :
      ‖∫ x in a..b, f (x + (t : ℂ) * Complex.I)‖ ≤ H t * |b-a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    apply hbound x
    rw [Set.uIoc_of_le hab] at hx
    exact ⟨hx.1.le,hx.2⟩
  apply mellin_contour_shift hab f hf
    (hline a ⟨le_rfl,hab⟩) (hline b ⟨hab,le_rfl⟩)
  · exact squeeze_zero_norm hedge (by simpa using hHtop.mul_const |b-a|)
  · have he : Tendsto (fun T : ℝ => ∫ x in a..b, f (x + ((-T : ℝ) : ℂ) * Complex.I))
        atTop (𝓝 0) :=
      squeeze_zero_norm (fun T => hedge (-T))
        (by simpa using (hHbot.comp tendsto_neg_atTop_atBot).mul_const |b-a|)
    simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using he

end CubicFirstMoment

end

end OAI
