import OAI.GroupTheory.PolycyclicRecognition.Analysis.HaarAveraging
import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace OAI

/-! # The positive autocorrelation behind backward recurrence -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

variable {G : Type*} [Group G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]

/-- Average a function over the inverse of a sampled right increment. -/
def rightInverseAverage (σ : Measure G) (f : G → ℝ≥0∞) (x : G) : ℝ≥0∞ :=
  ∫⁻ s, f (x * s⁻¹) ∂σ

theorem measurable_rightInverseAverage (σ : Measure G) [SFinite σ]
    {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (rightInverseAverage σ f) := by
  apply Measurable.lintegral_prod_right (f := fun x s : G => f (x * s⁻¹))
  exact hf.comp (measurable_fst.mul measurable_snd.inv)

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem rightInverseAverage_le_one (σ : Measure G) [IsProbabilityMeasure σ]
    {f : G → ℝ≥0∞} (hf : ∀ x, f x ≤ 1) (x : G) :
    rightInverseAverage σ f x ≤ 1 := by
  calc
    _ ≤ ∫⁻ _ : G, (1 : ℝ≥0∞) ∂σ := lintegral_mono (fun s => hf (x * s⁻¹))
    _ = 1 := by simp

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The averaged indicator vanishes outside the product of its original
set and a set carrying the increment law. This is the support bound used
in Cauchy--Schwarz. -/
theorem rightInverseAverage_indicator_eq_zero
    (σ : Measure G) (A K R : Set G) (hK : ∀ᵐ s ∂σ, s ∈ K)
    (hAR : ∀ a ∈ A, ∀ s ∈ K, a * s ∈ R) {x : G} (hx : x ∉ R) :
    rightInverseAverage σ (A.indicator (fun _ => (1 : ℝ≥0∞))) x = 0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hK] with s hs
  apply indicator_of_notMem
  intro hxs
  apply hx
  simpa only [inv_mul_cancel_right] using hAR (x * s⁻¹) hxs s hs

/-- The transition law obtained from two independent copies of the same
increment has nonnegative quadratic form. The square identity is exact and
uses right Haar invariance and Tonelli, with no symmetry assumption on σ. -/
theorem right_autocorrelation_eq_square
    (μ σ : Measure G) [SFinite μ] [SFinite σ] [μ.IsMulRightInvariant]
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x * (∫⁻ s, rightInverseAverage σ f (x * s) ∂σ) ∂μ) =
      ∫⁻ z, rightInverseAverage σ f z ^ 2 ∂μ := by
  have hA := measurable_rightInverseAverage σ hf
  have hprod : Measurable (fun p : G × G => f p.1 * rightInverseAverage σ f (p.1 * p.2)) :=
    (hf.comp measurable_fst).mul (hA.comp (measurable_fst.mul measurable_snd))
  calc
    _ = ∫⁻ x, ∫⁻ s, f x * rightInverseAverage σ f (x * s) ∂σ ∂μ := by
      apply lintegral_congr
      intro x
      exact (lintegral_const_mul _ (hA.comp (measurable_const.mul measurable_id))).symm
    _ = ∫⁻ s, ∫⁻ x, f x * rightInverseAverage σ f (x * s) ∂μ ∂σ :=
      lintegral_lintegral_swap hprod.aemeasurable
    _ = ∫⁻ s, ∫⁻ z, f (z * s⁻¹) * rightInverseAverage σ f z ∂μ ∂σ := by
      apply lintegral_congr
      intro s
      have h := lintegral_mul_right_eq_self (μ := μ)
        (fun z => f (z * s⁻¹) * rightInverseAverage σ f z) s
      simpa only [mul_inv_cancel_right] using h
    _ = ∫⁻ z, ∫⁻ s, f (z * s⁻¹) * rightInverseAverage σ f z ∂σ ∂μ := by
      apply lintegral_lintegral_swap
      exact ((hf.comp (measurable_snd.mul measurable_fst.inv)).mul
        (hA.comp measurable_snd)).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro z
      have hz : Measurable (fun s => f (z * s⁻¹)) :=
        hf.comp (measurable_const.mul measurable_inv)
      rw [lintegral_mul_const _ hz]
      simp only [pow_two, rightInverseAverage]

/-- The first averaged function has the same total mass as the original
one. This is the second input to the recurrence lower bound. -/
theorem lintegral_rightInverseAverage
    (μ σ : Measure G) [SFinite μ] [IsProbabilityMeasure σ] [μ.IsMulRightInvariant]
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, rightInverseAverage σ f z ∂μ) = ∫⁻ z, f z ∂μ := by
  change (∫⁻ z, ∫⁻ s, f (z * s⁻¹) ∂σ ∂μ) = _
  have hm : Measurable (fun p : G × G => f (p.1 * p.2⁻¹)) :=
    hf.comp (measurable_fst.mul measurable_snd.inv)
  rw [lintegral_lintegral_swap (f := fun z s : G => f (z * s⁻¹)) hm.aemeasurable]
  simp only [lintegral_mul_right_eq_self, lintegral_const, measure_univ, mul_one]

end PolycyclicRecognition

end

end OAI
