import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! The ordered likelihood-ratio comparison used by the folded Gaussian
transitions of the one-site Ising field recursion. -/

noncomputable section
open MeasureTheory Set

namespace InvariantIsing

/-- Ordered likelihood ratios increase every integrable increasing test.
The reference measure is supported on nonnegative absolute positions. -/
theorem field_likelihood_ratio_expectation_le
    (μ : Measure ℝ) [SFinite μ] (w₀ w₁ f : ℝ → ℝ)
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x)
    (hf : MonotoneOn f (Ici 0))
    (hcross : ∀ x ∈ Ici (0 : ℝ), ∀ y ∈ Ici (0 : ℝ), x ≤ y →
      w₁ x * w₀ y ≤ w₁ y * w₀ x)
    (hw₀ : Integrable w₀ μ) (hw₁ : Integrable w₁ μ)
    (hfw₀ : Integrable (fun x => f x * w₀ x) μ)
    (hfw₁ : Integrable (fun x => f x * w₁ x) μ)
    (hm₀ : 0 < ∫ x, w₀ x ∂μ) (hm₁ : 0 < ∫ x, w₁ x ∂μ) :
    (∫ x, f x * w₀ x ∂μ) / (∫ x, w₀ x ∂μ) ≤
      (∫ x, f x * w₁ x ∂μ) / (∫ x, w₁ x ∂μ) := by
  let K : ℝ × ℝ → ℝ := fun z =>
    (f z.1 * w₁ z.1) * w₀ z.2 + w₀ z.1 * (f z.2 * w₁ z.2) -
      (f z.1 * w₀ z.1) * w₁ z.2 - w₁ z.1 * (f z.2 * w₀ z.2)
  have hsupport : ∀ᵐ z ∂μ.prod μ, 0 ≤ z.1 ∧ 0 ≤ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_Ici.preimage measurable_fst).inter
        (measurableSet_Ici.preimage measurable_snd))).mpr
    filter_upwards [hμ] with x hx
    filter_upwards [hμ] with y hy
    exact ⟨hx, hy⟩
  have hK : 0 ≤ ∫ z, K z ∂μ.prod μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hsupport] with z hz
    have he : K z = (f z.1 - f z.2) * (w₁ z.1 * w₀ z.2 - w₀ z.1 * w₁ z.2) := by
      dsimp only [K]
      ring
    rw [he]
    rcases le_total z.1 z.2 with hxy | hyx
    · apply mul_nonneg_of_nonpos_of_nonpos
      · exact sub_nonpos.mpr (hf hz.1 hz.2 hxy)
      · have h := hcross z.1 hz.1 z.2 hz.2 hxy
        nlinarith
    · apply mul_nonneg
      · exact sub_nonneg.mpr (hf hz.2 hz.1 hyx)
      · have h := hcross z.2 hz.2 z.1 hz.1 hyx
        nlinarith
  have hI₁ := hfw₁.mul_prod hw₀
  have hI₂ := hw₀.mul_prod hfw₁
  have hI₃ := hfw₀.mul_prod hw₁
  have hI₄ := hw₁.mul_prod hfw₀
  have hI₁₂ : Integrable (fun z : ℝ × ℝ => (f z.1 * w₁ z.1) * w₀ z.2 +
      w₀ z.1 * (f z.2 * w₁ z.2)) (μ.prod μ) := hI₁.add hI₂
  have hI₁₂₃ : Integrable (fun z : ℝ × ℝ => (f z.1 * w₁ z.1) * w₀ z.2 +
      w₀ z.1 * (f z.2 * w₁ z.2) - (f z.1 * w₀ z.1) * w₁ z.2) (μ.prod μ) := hI₁₂.sub hI₃
  have he : (∫ z, K z ∂μ.prod μ) =
      2 * ((∫ x, f x * w₁ x ∂μ) * (∫ x, w₀ x ∂μ) -
        (∫ x, f x * w₀ x ∂μ) * (∫ x, w₁ x ∂μ)) := by
    dsimp only [K]
    rw [integral_sub hI₁₂₃ hI₄, integral_sub hI₁₂ hI₃, integral_add hI₁ hI₂]
    rw [integral_prod_mul (fun x => f x * w₁ x) w₀,
      integral_prod_mul w₀ (fun x => f x * w₁ x),
      integral_prod_mul (fun x => f x * w₀ x) w₁,
      integral_prod_mul w₁ (fun x => f x * w₀ x)]
    ring
  rw [he] at hK
  apply (div_le_div_iff₀ hm₀ hm₁).mpr
  linarith

end InvariantIsing

end

end OAI
