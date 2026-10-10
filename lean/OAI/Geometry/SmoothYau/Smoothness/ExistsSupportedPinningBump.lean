import Mathlib
import OAI.Geometry.SmoothYau.Limits.SupportedPinningTensor

namespace OAI

noncomputable section
namespace YauCounterexamples
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] [CompactSpace M]

lemma exists_supported_pinning_bump {A : Set M} (hA : IsOpen A) {x : M} (hx : x ∈ A) :
    ∃ χ : M → ℝ, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ ∧
      tsupport χ ⊆ A ∧ (∀ y, 0 ≤ χ y) ∧ χ x = 1 := by
  obtain ⟨V,hV,hxV,hVA⟩ := normal_exists_closure_subset isClosed_singleton hA
    (singleton_subset_iff.mpr hx)
  obtain ⟨χ,hχ1,hχ0,hχb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := 𝓘(ℝ,E)) (n := ⊤) isClosed_singleton (t := V)
    (by simpa only [hV.interior_eq] using hxV)
  refine ⟨χ,χ.contMDiff,?_,fun y => (hχb y).1,?_⟩
  · apply (closure_mono (show Function.support (fun y => χ y) ⊆ V from ?_)).trans hVA
    intro y hy
    by_contra hn
    exact hy (hχ0 y hn)
  · exact hχ1.self_of_nhdsSet x (mem_singleton x)

theorem exists_supported_separating_tensor [MeasurableSpace M] [OpensMeasurableSpace M]
    (μ : Measure M) [Measure.IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ]
    (g : SmoothMetric E M) {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) {A : Set M}
    (hA : IsOpen A) (hn : ∀ x ∈ A, metricGradient g u x ≠ 0)
    {x : M} (hx : x ∈ A) (hp : bundleTransverse g u x (metricGradient g v x) ≠ 0)
    (hd : Module.finrank ℝ E = 3) :
    ∃ χ : M → ℝ, tsupport χ ⊆ A ∧
      ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
        (fun y => TotalSpace.mk' (E →L[ℝ] E) y (supportedPinningTensor g u v χ y)) ∧
      (∀ y, LinearMap.trace ℝ (TangentSpace 𝓘(ℝ,E) y)
        (supportedPinningTensor g u v χ y).toLinearMap = 0) ∧
      (∀ y, supportedPinningTensor g u v χ y (metricGradient g u y) = 0) ∧
      0 < ∫ y, g.inner y (metricGradient g v y)
        (supportedPinningTensor g u v χ y (metricGradient g v y)) ∂μ := by
  obtain ⟨χ,hχ,hs,hχp,hχx⟩ := exists_supported_pinning_bump (E := E) hA hx
  have hnp (y : M) (hy : χ y ≠ 0) : metricGradient g u y ≠ 0 :=
    hn y (hs (subset_closure hy))
  have hK := supportedPinningTensor_smooth g hu hv hχ hA hs hn
  have hq : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (fun y => g.inner y (metricGradient g v y)
      (supportedPinningTensor g u v χ y (metricGradient g v y))) := by
    intro y
    have hh := (g.contMDiff y).clm_bundle_apply₂ (contMDiff_metricGradient g hv y)
      ((hK y).clm_bundle_apply (contMDiff_metricGradient g hv y))
    rw [contMDiffAt_totalSpace] at hh
    exact hh.2
  refine ⟨χ,hs,hK,fun y => supportedPinningTensor_trace g u v χ y (hnp y) hd,
    fun y => supportedPinningTensor_kernel g u v χ y (hnp y),?_⟩
  have hnonneg : 0 ≤ (fun y => g.inner y (metricGradient g v y)
      (supportedPinningTensor g u v χ y (metricGradient g v y))) := by
    intro y
    change 0 ≤ g.inner y (metricGradient g v y)
      (supportedPinningTensor g u v χ y (metricGradient g v y))
    rw [supportedPinningTensor_quadratic g u v χ y (hnp y)]
    exact mul_nonneg (div_nonneg (hχp y) (by norm_num)) (sq_nonneg _)
  exact hq.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) hnonneg
    (supportedPinningTensor_quadratic_pos g u v χ x (by rw [hχx]; norm_num)
      (hn x hx) hp).ne'
end YauCounterexamples

end

end OAI
