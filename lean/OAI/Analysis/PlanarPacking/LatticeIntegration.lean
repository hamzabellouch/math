import OAI.Analysis.PlanarPacking.LatticeGaussian
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
lemma lattice_integral_hasSum {μ : Measure ℝ} {f : ℝ→ℂ} (hf : Integrable f μ)
    {K : (ℤ×ℤ)→ℝ→ℂ} (hK : ∀ p, AEStronglyMeasurable (K p) μ)
    {C : (ℤ×ℤ)→ℝ} (hC : Summable C)
    (hb : ∀ᵐ t ∂μ, ∀ p, ‖K p t‖≤C p) :
    HasSum (fun p => ∫ t, K p t*f t ∂μ)
      (∫ t, (∑' p, K p t)*f t ∂μ) := by
  apply hasSum_integral_of_dominated_convergence (fun p t => C p*‖f t‖)
  · intro p; exact (hK p).mul hf.aestronglyMeasurable
  · intro p
    filter_upwards [hb] with t ht
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (ht p) (norm_nonneg _)
  · exact Filter.Eventually.of_forall fun t => hC.mul_right ‖f t‖
  · simpa only [tsum_mul_right] using hf.norm.const_mul (∑' p, C p)
  · filter_upwards [hb] with t ht
    have hs : Summable (fun p => K p t) := Summable.of_norm_bounded hC (ht)
    exact hs.hasSum.mul_right (f t)
lemma lattice_direct_hasSum {μ : Measure ℝ} {f : ℝ→ℂ} (hf : Integrable f μ) :
    HasSum (fun p : ℤ×ℤ => gaussianSpectral μ f (latticePoint p))
      (∫ t, (∑' p : ℤ×ℤ, spectralGaussian t (latticePoint p))*f t ∂μ) := by
  apply lattice_integral_hasSum hf
    (fun p => ((spectralGaussian_continuous.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable)
    latticeDamping_summable
  exact Filter.Eventually.of_forall fun t p => (lattice_spectral_bound t p).le
lemma lattice_transform_hasSum {μ : Measure ℝ} [SFinite μ] {f : ℝ→ℂ}
    (hf : Integrable f μ) (ht : ∀ᵐ t ∂μ, |t|≤1) :
    HasSum (fun p : ℤ×ℤ => 𝓕 (gaussianSpectral μ f) (latticePoint p))
      (∫ t, (∑' p : ℤ×ℤ, 𝓕 (spectralGaussian t) (latticePoint p))*f t ∂μ) := by
  have hm (p : ℤ×ℤ) : AEStronglyMeasurable (fun t : ℝ => 𝓕 (spectralGaussian t) (latticePoint p)) μ := by
    simp_rw [spectralGaussian_fourier]
    exact (continuous_const.mul (continuous_kernelMoment 0 _)).aestronglyMeasurable
  have hh := lattice_integral_hasSum hf hm
    (latticeDamping_summable.mul_left (1/(b*h)))
    (ht.mono fun t ht p => lattice_fourier_spectral_bound ht p)
  convert hh using 1
  funext p
  exact spectralGaussian_fourier_integral hf (latticePoint p)
lemma gaussianSpectral_hex_poisson {μ : Measure ℝ} [SFinite μ] {f : ℝ→ℂ}
    (hf : Integrable f μ) (ht : ∀ᵐ t ∂μ, |t|≤1) :
    (∑' p : ℤ×ℤ, gaussianSpectral μ f (latticePoint p)) =
      ∑' p : ℤ×ℤ, 𝓕 (gaussianSpectral μ f) (latticePoint p) := by
  rw [(lattice_direct_hasSum hf).tsum_eq,(lattice_transform_hasSum hf ht).tsum_eq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => congrArg (fun z : ℂ => z*f t) (spectralGaussian_hex_poisson t)
end SharpPlanar

end OAI
