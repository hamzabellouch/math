import OAI.Analysis.CircleDomains.Modulus.WeightedPhysicalChart
import OAI.Analysis.CircleDomains.Topology.CompactLevelCount
import OAI.Analysis.CircleDomains.Probability.PhysicalOccupationCost

namespace OAI

/-! Mean distinct intersections with a smooth circle-valued coordinate
on a compact physical chart. The bound is against the actual mean
occupation of the original quotient-path law. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [SecondCountableTopology X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem mean_smooth_physical_chart_circle_count_le
    (hcoarea : PlanarLipschitzFiberCoarea)
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) (hφ : Continuous φ) {A D : Set ℂ} (hA : IsCompact A)
    (hAG : MapsTo φ A G) (hAD : A ⊆ D) (hD : IsOpen D)
    (j : Y → ℂ) (hjm : Measurable j) (hj : ∀ z ∈ A, j (φ z) = z)
    (B : ℝ≥0) (hB : LipschitzOnWith B j (φ '' A))
    (K : Set C(PathTime, X)) (hK : ∀ γ ∈ K, Injective γ)
    (η : ProbabilityMeasure K)
    (hfinite : ∀ γ ∈ K, physicalDomainLength e y₀ γ < ∞)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    (∫⁻ t in Ico (0 : ℝ) 1, ∫⁻ γ : K,
      pathImageCount ((π ∘ φ) '' (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)}))
        γ.val ∂(η : Measure K)) ≤
      (B : ℝ≥0∞) * ∫⁻ y in φ '' A, ENNReal.ofReal ‖fderiv ℝ f (j y)‖
        ∂meanPhysicalOccupation e y₀ (η.map Subtype.val) := by
  have hφA := (hA.image hφ).measurableSet
  let g : Y → ℝ≥0∞ := (φ '' A).indicator (fun y => ENNReal.ofReal ‖fderiv ℝ f (j y)‖)
  have hg : Measurable g :=
    (((measurable_fderiv ℝ f).norm.ennreal_ofReal).comp hjm).indicator hφA
  have hcount := measurable_compact_chart_circle_count (π ∘ φ) (hπ.comp hφ) hA f
    (hf.continuousOn.mono hAD) K hK
  have hm : Measurable (fun p : K × ℝ =>
      pathImageCount ((π ∘ φ) '' (A ∩ {z | (f z : UnitAddCircle) = (p.2 : UnitAddCircle)}))
        p.1.val) := hcount.comp (measurable_fst.prodMk
          ((AddCircle.continuous_mk' (1 : ℝ)).measurable.comp measurable_snd))
  have hp (γ : K) : (∫⁻ t in Ico (0 : ℝ) 1,
      pathImageCount ((π ∘ φ) '' (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)})) γ.val) ≤
      (B : ℝ≥0∞) * ∫⁻ y, g y ∂physicalOccupationCode e y₀ γ.val := by
    rw [show (∫⁻ y, g y ∂physicalOccupationCode e y₀ γ.val) =
      ∫⁻ y in φ '' A, ENNReal.ofReal ‖fderiv ℝ f (j y)‖ ∂physicalOccupationCode e y₀ γ.val
      from lintegral_indicator hφA _, physicalOccupationCode_eq e y₀ ⟨γ.val, hfinite γ.val γ.property⟩]
    exact smooth_physical_chart_circle_count_le hcoarea e hU y₀ π hπ he φ hφ hA.measurableSet
      hφA hAG hAD hD j hjm hj B hB ⟨γ.val, hfinite γ.val γ.property⟩ hf
  have hmean : (∫⁻ γ : K, ∫⁻ y, g y ∂physicalOccupationCode e y₀ γ.val ∂(η : Measure K)) =
      ∫⁻ y, g y ∂meanPhysicalOccupation e y₀ (η.map Subtype.val) := by
    rw [← lintegral_physicalOccupationCode e hU y₀ (η.map Subtype.val) g hg,
      ProbabilityMeasure.toMeasure_map, lintegral_map]
    · exact (Measure.measurable_lintegral hg).comp (measurable_physicalOccupationCode e hU y₀)
    · exact measurable_subtype_coe
  calc
    _ = ∫⁻ γ : K, ∫⁻ t in Ico (0 : ℝ) 1,
        pathImageCount ((π ∘ φ) '' (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)}))
          γ.val ∂volume ∂(η : Measure K) :=
      lintegral_lintegral_swap (hm.comp measurable_swap).aemeasurable
    _ ≤ ∫⁻ γ : K, (B : ℝ≥0∞) * ∫⁻ y, g y ∂physicalOccupationCode e y₀ γ.val
        ∂(η : Measure K) := lintegral_mono hp
    _ = (B : ℝ≥0∞) * ∫⁻ y, g y ∂meanPhysicalOccupation e y₀ (η.map Subtype.val) := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, hmean]
    _ = _ := by rw [show g = (φ '' A).indicator
      (fun y => ENNReal.ofReal ‖fderiv ℝ f (j y)‖) from rfl, lintegral_indicator hφA]

end CircleDomainRigidity

end

end OAI
