import OAI.Probability.SLE.Geometry.RandomSpatialTesting
import OAI.Probability.SLE.LoewnerCharts

namespace OAI

/-! Nonnegative random tests of locally finite half-plane measures.
Compact restrictions remove any need for a finite total mass. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal

namespace SLEExactGauge

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

private lemma finite_halfPlane_random_test_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Ω → Measure upperHalfPlane) (hμ : Measurable μ)
    (hfin : ∀ ω, IsFiniteMeasure (μ ω))
    (f : Ω × upperHalfPlane → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun ω => ∫⁻ z, f (ω,z) ∂μ ω) := by
  let K : Kernel Ω upperHalfPlane := ⟨μ,hμ⟩
  have hp : Measurable (fun ω => (μ ω).map (Prod.mk ω)) := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have h := Kernel.measurable_kernel_prodMk_left_of_finite (κ := K) hA hfin
    change Measurable (fun a => μ a (Prod.mk a ⁻¹' A)) at h
    simpa only [Measure.map_apply measurable_prodMk_left hA] using h
  have h := (Measure.measurable_lintegral hf).comp hp
  convert h using 1
  funext ω
  exact (lintegral_map hf measurable_prodMk_left).symm

theorem halfPlane_random_test_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Ω → Measure upperHalfPlane) (hμ : Measurable μ)
    (hfin : ∀ ω, IsFiniteMeasureOnCompacts (μ ω))
    (f : Ω × upperHalfPlane → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun ω => ∫⁻ z, f (ω,z) ∂μ ω) := by
  have he (ω : Ω) : (∫⁻ z, f (ω,z) ∂μ ω) =
      ⨆ n, ∫⁻ z in compactCovering upperHalfPlane n, f (ω,z) ∂μ ω := by
    rw [← setLIntegral_iUnion_of_directed _ (Monotone.directed_le (compactCovering_subset upperHalfPlane)),
      iUnion_compactCovering,Measure.restrict_univ]
  simp_rw [he]
  apply Measurable.iSup
  intro n
  have hK := (isCompact_compactCovering upperHalfPlane n).measurableSet
  have hm : Measurable (fun ω => (μ ω).restrict (compactCovering upperHalfPlane n)) := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    simp only [Measure.restrict_apply hA]
    exact (Measure.measurable_coe (hA.inter hK)).comp hμ
  apply finite_halfPlane_random_test_measurable _ hm _ f hf
  intro ω
  let := hfin ω
  exact ⟨by simpa only [Measure.restrict_apply_univ] using
    (isCompact_compactCovering upperHalfPlane n).measure_lt_top (μ := μ ω)⟩

end SLEExactGauge

end

end OAI
