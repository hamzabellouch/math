import OAI.Probability.InvariantIsing.Spectral.CompactResolventTests
import OAI.Probability.InvariantIsing.Spectral.SpectralClipping

namespace OAI

/-! Clipped spectral probability laws on their compact interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace InvariantIsing

def compactSpectralClip (R : ℝ) (hR : 0 ≤ R) (x : ℝ) : Icc (0 : ℝ) R :=
  ⟨spectralClip 0 R x,spectralClip_mem hR x⟩

lemma continuous_compactSpectralClip (R : ℝ) (hR : 0 ≤ R) : Continuous (compactSpectralClip R hR) :=
  (continuous_spectralClip 0 R).subtype_mk _

def compactClippedLaw (R : ℝ) (hR : 0 ≤ R) (μ : ProbabilityMeasure ℝ) :
    ProbabilityMeasure (Icc (0 : ℝ) R) := μ.map (compactSpectralClip R hR)

lemma compactClippedLaw_real (R : ℝ) (hR : 0 ≤ R) (μ : ProbabilityMeasure ℝ) :
    (compactClippedLaw R hR μ).map (fun x => (x : ℝ)) = μ.map (spectralClip 0 R) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [compactClippedLaw,ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map measurable_subtype_coe (continuous_compactSpectralClip R hR).measurable]
  rfl

lemma compactClippedLaw_integral (R : ℝ) (hR : 0 ≤ R) (μ : ProbabilityMeasure ℝ)
    (t : {t : ℝ // 0 < t}) :
    (∫ x, compactResolventTest R t x ∂(compactClippedLaw R hR μ : Measure _)) =
      ∫ x, positiveResolventTest t (spectralClip 0 R x) ∂(μ : Measure ℝ) := by
  rw [compactClippedLaw,ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_compactSpectralClip R hR).measurable.aemeasurable
      (compactResolventTest R t).continuous.aestronglyMeasurable]
  rfl

lemma compactClippedLaw_real_eq (R : ℝ) (hR : 0 ≤ R) (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) R) :
    (compactClippedLaw R hR μ).map (fun x => (x : ℝ)) = μ := by
  rw [compactClippedLaw_real]
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  calc
    (μ : Measure ℝ).map (spectralClip 0 R) = (μ : Measure ℝ).map id :=
      Measure.map_congr (hμ.mono fun _ hx => spectralClip_eq hx)
    _ = μ := Measure.map_id

end InvariantIsing

end

end OAI
