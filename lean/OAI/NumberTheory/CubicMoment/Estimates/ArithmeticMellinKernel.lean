import OAI.NumberTheory.CubicMoment.Estimates.NormMellinMoments

namespace OAI

/-! Convert the Fourier-transform frequency to the arithmetic height in
N(n)^(it). The fixed factor 2π stays in the actual kernel. -/
noncomputable section
open scoped ContDiff FourierTransform SchwartzMap
open Set MeasureTheory
namespace CubicFirstMoment

def arithmeticMellinCoefficient (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (ρ t : ℝ) : ℂ :=
  normDenominatorMellinCoefficient M hM V hV hV' ρ (t/(2*Real.pi))

lemma arithmeticMellinCoefficient_continuous (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (ρ : ℝ) :
    Continuous (arithmeticMellinCoefficient M hM V hV hV' ρ) :=
  (𝓕 (normDenominatorLogSchwartz M hM V hV hV' ρ)).continuous.comp
    (continuous_id.div_const _)

lemma arithmeticMellinCoefficient_integrable (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (ρ : ℝ) :
    Integrable (arithmeticMellinCoefficient M hM V hV hV' ρ) :=
  (normDenominatorMellinCoefficient_integrable M hM V hV hV' ρ).comp_div
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)

theorem arithmeticMellinCoefficient_quadratic_decay (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ ρ : ℝ, 0 ≤ ρ → ∀ t : ℝ,
      (1+ρ)^q*‖t‖^2*‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖ ≤ D := by
  obtain ⟨C,hC,hb⟩ := normDenominatorMellinCoefficient_pointwise_rapidDecay M hM V hV hV' q 2
  have hc : 2*Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  refine ⟨C*(2*Real.pi)^2,mul_pos hC (sq_pos_of_ne_zero hc),?_⟩
  intro ρ hρ t
  have h := mul_le_mul_of_nonneg_right (hb ρ hρ (t/(2*Real.pi))) (sq_nonneg (2*Real.pi))
  convert h using 1
  simp only [arithmeticMellinCoefficient,Real.norm_eq_abs,sq_abs,div_pow]
  field_simp

end CubicFirstMoment

end

end OAI
