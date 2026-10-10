import OAI.Combinatorics.Progressions.Probability.JointProductiveMeasure

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem centeredFiniteProbabilityMeasure_integral_reference_comparison
    {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    (f : Ω → ℝ) (hf : Measurable f) {M a ε : ℝ}
    (hbound : ∀ x, ‖f x‖ ≤ M)
    (hcompare : ∀ c, |(law c).mean f - a| ≤ ε) :
    |(∫ z, f z.2 ∂centeredFiniteProbabilityMeasure μ law) - a| ≤ ε := by
  rw [centeredFiniteProbabilityMeasure_integral_bounded μ law hweight
    (fun z => f z.2) (hf.comp measurable_snd) (fun z => hbound z.2)]
  have hi := centeredFinite_mean_integrable μ law hweight (fun _ x => f x)
    (fun _ => integrable_const _)
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun c => (law c).mean f - a)
    (ae_of_all μ (fun c => by simpa only [Real.norm_eq_abs] using hcompare c))
  simpa only [integral_sub hi (integrable_const a), integral_const, probReal_univ,
    one_smul, mul_one, Real.norm_eq_abs] using h

end Erdos3

end

end OAI
