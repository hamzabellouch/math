import OAI.Analysis.CircleDomains.Sobolev.MeanSmoothPhysicalCount
import OAI.Analysis.CircleDomains.Topology.CountableClosedLevelCount

namespace OAI

/-! Differential-weighted mean intersection bounds on an open physical
chart, exhausted by compact sets. The law may contain paths with repeats.
-/

open Set Function MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [SecondCountableTopology X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem mean_sigmaCompact_physical_chart_circle_count_le
    (hcoarea : PlanarLipschitzFiberCoarea)
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) (hφ : Continuous φ) {A D : Set ℂ} (hA : IsSigmaCompact A)
    (hAG : MapsTo φ A G) (hAD : A ⊆ D) (hD : IsOpen D)
    (j : Y → ℂ) (hjm : Measurable j) (hj : ∀ z ∈ A, j (φ z) = z)
    (B : ℝ≥0) (hB : LipschitzOnWith B j (φ '' A))
    (μ : ProbabilityMeasure C(PathTime, X))
    (hfinite : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)), physicalDomainLength e y₀ γ < ∞)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    (∫⁻ t in Ico (0 : ℝ) 1, ∫⁻ γ : C(PathTime, X),
      pathImageCount ((π ∘ φ) '' (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)}))
        γ ∂(μ : Measure C(PathTime, X))) ≤
      (B : ℝ≥0∞) * ∫⁻ y in φ '' A, ENNReal.ofReal ‖fderiv ℝ f (j y)‖
        ∂meanPhysicalOccupation e y₀ μ := by
  have hAm : MeasurableSet A := by
    obtain ⟨K, hK, hcov⟩ := hA
    rw [← hcov]
    exact MeasurableSet.iUnion fun n => (hK n).measurableSet
  have hφA : MeasurableSet (φ '' A) := by
    obtain ⟨K, hK, hcov⟩ := hA.image hφ
    rw [← hcov]
    exact MeasurableSet.iUnion fun n => (hK n).measurableSet
  let g : Y → ℝ≥0∞ := (φ '' A).indicator (fun y => ENNReal.ofReal ‖fderiv ℝ f (j y)‖)
  have hg : Measurable g :=
    (((measurable_fderiv ℝ f).norm.ennreal_ofReal).comp hjm).indicator hφA
  have hcount := measurable_sigmaCompact_chart_circle_count (π ∘ φ) (hπ.comp hφ) hA f
    (hf.continuousOn.mono hAD)
  have hm : Measurable (fun p : C(PathTime, X) × ℝ =>
      pathImageCount ((π ∘ φ) '' (A ∩ {z | (f z : UnitAddCircle) = (p.2 : UnitAddCircle)}))
        p.1) := hcount.comp (measurable_fst.prodMk
          ((AddCircle.continuous_mk' (1 : ℝ)).measurable.comp measurable_snd))
  have hp : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)), (∫⁻ t in Ico (0 : ℝ) 1,
      pathImageCount ((π ∘ φ) '' (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)})) γ) ≤
      (B : ℝ≥0∞) * ∫⁻ y, g y ∂physicalOccupationCode e y₀ γ := by
    filter_upwards [hfinite] with γ hγ
    rw [show (∫⁻ y, g y ∂physicalOccupationCode e y₀ γ) =
      ∫⁻ y in φ '' A, ENNReal.ofReal ‖fderiv ℝ f (j y)‖ ∂physicalOccupationCode e y₀ γ
      from lintegral_indicator hφA _, physicalOccupationCode_eq e y₀ ⟨γ, hγ⟩]
    exact smooth_physical_chart_circle_count_le hcoarea e hU y₀ π hπ he φ hφ hAm
      hφA hAG hAD hD j hjm hj B hB ⟨γ, hγ⟩ hf
  calc
    _ = ∫⁻ γ : C(PathTime, X), ∫⁻ t in Ico (0 : ℝ) 1,
        pathImageCount ((π ∘ φ) '' (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)}))
          γ ∂volume ∂(μ : Measure C(PathTime, X)) :=
      lintegral_lintegral_swap (hm.comp measurable_swap).aemeasurable
    _ ≤ ∫⁻ γ : C(PathTime, X), (B : ℝ≥0∞) * ∫⁻ y, g y ∂physicalOccupationCode e y₀ γ
        ∂(μ : Measure C(PathTime, X)) := lintegral_mono_ae hp
    _ = (B : ℝ≥0∞) * ∫⁻ y, g y ∂meanPhysicalOccupation e y₀ μ := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
        lintegral_physicalOccupationCode e hU y₀ μ g hg]
    _ = _ := by rw [show g = (φ '' A).indicator
      (fun y => ENNReal.ofReal ‖fderiv ℝ f (j y)‖) from rfl, lintegral_indicator hφA]

end CircleDomainRigidity

end

end OAI
