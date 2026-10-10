import OAI.Analysis.Pureness.Comparison.SpectralMeasure
import OAI.Analysis.Pureness.Comparison.IntegerCuts
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI
open scoped ENNReal BigOperators
open MeasureTheory Filter Set CompactlySupported CompactlySupportedContinuousMap
namespace CuntzComparison
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma TracialState.integrable_spectralMeasure (τ : TracialState A)
    (a : A) (ha : IsSelfAdjoint a) (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable f (τ.spectralMeasure a ha) := by
  let g : C_c(spectrum ℝ a, ℝ) :=
    ⟨⟨fun t => f t, hf.comp continuous_subtype_val⟩, HasCompactSupport.of_compactSpace _⟩
  apply (integrable_map_measure hf.aestronglyMeasurable (by fun_prop)).mpr
  exact g.integrable

lemma TracialState.ae_mem_spectrum (τ : TracialState A) (a : A) (ha : IsSelfAdjoint a) :
    ∀ᵐ t ∂(τ.spectralMeasure a ha), t ∈ spectrum ℝ a := by
  unfold TracialState.spectralMeasure
  apply (ae_map_iff (p := fun t => t ∈ spectrum ℝ a) (by fun_prop)
    (spectrum.isClosed (𝕜 := ℝ) a).measurableSet).mpr
  exact Eventually.of_forall fun t => t.property

lemma TracialState.spectralMeasure_univ (τ : TracialState A) (a : A) (ha : IsSelfAdjoint a) :
    τ.spectralMeasure a ha univ = 1 := by
  have h := τ.integral_spectralMeasure a ha (fun _ => 1) continuous_const
  rw [cfc_const_one ℝ a ha, τ.normalized] at h
  simp only [integral_const, smul_eq_mul, mul_one, Complex.one_re] at h
  exact (ENNReal.toReal_eq_one_iff _).mp h

instance (τ : TracialState A) (a : A) (ha : IsSelfAdjoint a) :
    IsProbabilityMeasure (τ.spectralMeasure a ha) := ⟨τ.spectralMeasure_univ a ha⟩

lemma TracialState.spectralSupportMass_le_one (τ : TracialState A) (a : A) (ha : 0 ≤ a) :
    τ.spectralSupportMass a ha ≤ 1 := by
  unfold TracialState.spectralSupportMass
  exact prob_le_one

lemma integrable_strictCut (μ : Measure ℝ) [IsFiniteMeasure μ] (r : ℝ) :
    Integrable (fun t : ℝ => if r < t then (1 : ℝ) else 0) μ := by
  change Integrable ((Ioi r).indicator (fun _ : ℝ => (1 : ℝ))) μ
  exact (integrable_const (1 : ℝ)).indicator measurableSet_Ioi

lemma integral_strictCut (μ : Measure ℝ) [IsFiniteMeasure μ] (r : ℝ) :
    ∫ t : ℝ, (if r < t then (1 : ℝ) else 0) ∂μ = (μ (Ioi r)).toReal := by
  simpa [Set.indicator, Set.mem_Ioi, Measure.real] using
    (integral_indicator_one (μ := μ) (measurableSet_Ioi (a := r)))

lemma integrable_integerCutCount (μ : Measure ℝ) [IsFiniteMeasure μ] (L : ℕ) :
    Integrable (integerCutCount L) μ := by
  unfold integerCutCount
  exact integrable_finsetSum _ fun j hj => integrable_strictCut μ (j + 1 : ℕ)

lemma integral_integerCutCount (μ : Measure ℝ) [IsFiniteMeasure μ] (L : ℕ) :
    ∫ t, integerCutCount L t ∂μ = ∑ j ∈ Finset.range L, (μ (Ioi (j + 1 : ℕ))).toReal := by
  unfold integerCutCount
  rw [integral_finsetSum _ (fun j hj => integrable_strictCut μ (j + 1 : ℕ))]
  exact Finset.sum_congr rfl fun j hj => integral_strictCut μ (j + 1 : ℕ)

theorem TracialState.integer_spectral_trace_error (τ : TracialState A)
    {a : A} (ha : 0 ≤ a) {L : ℕ} (hL : ‖a‖ ≤ L) :
    0 ≤ (τ.toPositiveLinearMap a).re -
        ∑ j ∈ Finset.range L, (τ.spectralMeasure a ha.isSelfAdjoint (Ioi (j + 1 : ℕ))).toReal ∧
    (τ.toPositiveLinearMap a).re -
        ∑ j ∈ Finset.range L, (τ.spectralMeasure a ha.isSelfAdjoint (Ioi (j + 1 : ℕ))).toReal ≤
      (τ.spectralSupportMass a ha).toReal := by
  have h01 : (0 : A) ≠ 1 := by
    intro h
    have hz : (0 : ℂ) = 1 := by simpa [τ.normalized] using congrArg τ.toPositiveLinearMap h
    exact zero_ne_one hz
  let : Nontrivial A := ⟨⟨0, 1, h01⟩⟩
  let μ := τ.spectralMeasure a ha.isSelfAdjoint
  have hid := τ.integrable_spectralMeasure a ha.isSelfAdjoint (fun t => t) continuous_id
  have hcnt := integrable_integerCutCount μ L
  have hcut := integrable_strictCut μ 0
  have hpoint : ∀ᵐ t ∂μ, 0 ≤ t - integerCutCount L t ∧
      t - integerCutCount L t ≤ if 0 < t then (1 : ℝ) else 0 := by
    filter_upwards [τ.ae_mem_spectrum a ha.isSelfAdjoint] with t ht
    have ht0 := spectrum_nonneg_of_nonneg ha ht
    have htL := (Real.le_norm_self t).trans ((spectrum.norm_le_norm_of_mem ht).trans hL)
    exact integer_cuts ht0 htL
  have heq : ∫ t, t - integerCutCount L t ∂μ = (τ.toPositiveLinearMap a).re -
      ∑ j ∈ Finset.range L, (μ (Ioi (j + 1 : ℕ))).toReal := by
    rw [integral_sub hid hcnt, integral_integerCutCount]
    have h := τ.integral_spectralMeasure a ha.isSelfAdjoint (fun t => t) continuous_id
    simpa only [cfc_id' ℝ a] using congrArg
      (fun v => v - ∑ j ∈ Finset.range L, (μ (Ioi (j + 1 : ℕ))).toReal) h
  constructor
  · rw [← heq]
    exact integral_nonneg_of_ae (hpoint.mono fun t ht => ht.1)
  · rw [← heq]
    have h := integral_mono_ae (hid.sub hcnt) hcut (hpoint.mono fun t ht => ht.2)
    rw [integral_strictCut] at h
    exact h
end CuntzComparison

end OAI
