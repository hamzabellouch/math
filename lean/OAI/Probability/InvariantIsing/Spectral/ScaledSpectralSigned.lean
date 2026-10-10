import OAI.Probability.InvariantIsing.Spectral.ScaledSpectralLaw

namespace OAI

/-! Spectral support under a scalar of either sign. -/
noncomputable section
open MeasureTheory Set
namespace InvariantIsing

lemma signed_scaled_spectral_support (ν : ProbabilityMeasure ℝ) (a b c : ℝ)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b) :
    (scaledSpectralLaw ν c : Measure ℝ).support ⊆
      Icc (min (c*a) (c*b)) (max (c*a) (c*b)) := by
  apply Measure.support_subset_of_isClosed isClosed_Icc
  change ∀ᵐ y ∂((ν : Measure ℝ).map (fun x => c*x)),
    y∈Icc (min (c*a) (c*b)) (max (c*a) (c*b))
  apply (ae_map_iff (measurable_const.mul measurable_id).aemeasurable measurableSet_Icc).mpr
  filter_upwards [(ν : Measure ℝ).support_mem_ae] with x hx
  by_cases hc : 0 ≤ c
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left (hbound hx).1 hc),
      (mul_le_mul_of_nonneg_left (hbound hx).2 hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left (hbound hx).2 (le_of_not_ge hc)),
      (mul_le_mul_of_nonpos_left (hbound hx).1 (le_of_not_ge hc)).trans (le_max_left _ _)⟩

lemma signed_scaled_spectral_endpoints (ν : ProbabilityMeasure ℝ) (a b c : ℝ)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support) :
    min (c*a) (c*b)∈(scaledSpectralLaw ν c : Measure ℝ).support ∧
    max (c*a) (c*b)∈(scaledSpectralLaw ν c : Measure ℝ).support := by
  by_cases h : c*a ≤ c*b
  · simpa only [min_eq_left h,max_eq_right h] using
      And.intro (scaled_spectral_support_mem ν c a ha) (scaled_spectral_support_mem ν c b hb)
  · simpa only [min_eq_right (le_of_not_ge h),max_eq_left (le_of_not_ge h)] using
      And.intro (scaled_spectral_support_mem ν c b hb) (scaled_spectral_support_mem ν c a ha)

end InvariantIsing

end

end OAI
