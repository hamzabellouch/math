import OAI.Probability.FreeIsing.Energy.TiltedVariance
import OAI.Probability.FreeIsing.Gaussian.LinearSignalTilt

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma memLp_two_linearSignalTilt [IsProbabilityMeasure μ]
    {q g : Ω → ℝ} {a : ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ x ∂μ, |q x| ≤ 1) (ha : |a| ≤ 1) (hg : MemLp g 2 μ) :
    MemLp g 2 (linearSignalTilt μ q a) := by
  have hgi := integrable_linearSignalTilt hq hqb ha (hg.integrable one_le_two)
  exact (memLp_two_iff_integrable_sq hgi.aestronglyMeasurable).mpr
    (integrable_linearSignalTilt hq hqb ha hg.integrable_sq)

lemma variance_linearSignalTilt_ge [IsProbabilityMeasure μ]
    {q g : Ω → ℝ} {a : ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ x ∂μ, |q x| ≤ 1) (ha : |a| ≤ 1) (hg : MemLp g 2 μ)
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hqodd : ∀ᵐ x ∂μ, q (T x) = -q x)
    (hgodd : ∀ᵐ x ∂μ, g (T x) = -g x) :
    (1 - a ^ 2) * (∫ x, g x ^ 2 ∂μ) ≤ variance g (linearSignalTilt μ q a) := by
  let := linearSignalTilt_probability hq hqb ha
    (integral_eq_zero_of_ae_sign_reversal T hT hqodd)
  apply variance_ge_of_binary_tilt_moments hg
    (memLp_two_linearSignalTilt hq hqb ha hg) hq.aestronglyMeasurable hqb
  · rw [integral_linearSignalTilt hq hqb ha (hg.integrable one_le_two),
      integral_eq_zero_of_ae_sign_reversal T hT hgodd, zero_add]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  · apply integral_linearSignalTilt_ae_even hq hqb ha hg.integrable_sq T hT hqodd
    filter_upwards [hgodd] with x hx
    rw [hx, neg_sq]

lemma variance_linearSignalTilt_ge_signal_moment [IsProbabilityMeasure μ]
    {q g : Ω → ℝ} {a theta : ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ x ∂μ, |q x| ≤ 1) (ha : |a| ≤ 1) (hg : MemLp g 2 μ)
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hqodd : ∀ᵐ x ∂μ, q (T x) = -q x)
    (hgodd : ∀ᵐ x ∂μ, g (T x) = -g x)
    (haTheta : a ^ 2 ≤ theta ^ 2) (hTheta : theta ^ 2 ≤ 1)
    (hdom : ∀ᵐ x ∂μ, theta ^ 2 * q x ^ 2 ≤ g x ^ 2) :
    (1 - theta ^ 2) * theta ^ 2 * (∫ x, q x ^ 2 ∂μ) ≤
      variance g (linearSignalTilt μ q a) := by
  have hqLp : MemLp q 2 μ :=
    MemLp.of_bound hq.aestronglyMeasurable 1 (by simpa only [Real.norm_eq_abs] using hqb)
  have henergy : theta ^ 2 * (∫ x, q x ^ 2 ∂μ) ≤ ∫ x, g x ^ 2 ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono_ae (hqLp.integrable_sq.const_mul _) hg.integrable_sq hdom
  have hnonneg : 0 ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  calc
    (1 - theta ^ 2) * theta ^ 2 * (∫ x, q x ^ 2 ∂μ) =
        (1 - theta ^ 2) * (theta ^ 2 * (∫ x, q x ^ 2 ∂μ)) := by ring
    _ ≤ (1 - theta ^ 2) * (∫ x, g x ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left henergy (sub_nonneg.mpr hTheta)
    _ ≤ (1 - a ^ 2) * (∫ x, g x ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_right (sub_le_sub_left haTheta 1) hnonneg
    _ ≤ _ := variance_linearSignalTilt_ge hq hqb ha hg T hT hqodd hgodd

end Problem367

end

end OAI
