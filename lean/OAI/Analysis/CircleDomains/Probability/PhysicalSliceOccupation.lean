import OAI.Analysis.CircleDomains.Sobolev.CompactPhysicalFiberCoarea
import OAI.Analysis.CircleDomains.Probability.PhysicalOccupationCode

namespace OAI

/-! The physical occupation measure controls compact physical slices. A local inverse chart bound suffices; no regularity
of the Jordan coordinate change is used. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

omit [MeasurableSpace Y] [BorelSpace Y] in
 theorem physical_chart_image_subset (e : G ≃ₜ U) (y₀ : Y)
    (π : Y → X) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) {A : Set ℂ} (hA : MapsTo φ A G) (γ : C(PathTime, X)) :
    φ '' (A ∩ (π ∘ φ) ⁻¹' range γ) ⊆
      (physicalValue e y₀ ∘ γ) '' (γ ⁻¹' U) := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨t, ht⟩ := hz.2
  have hez := he ⟨φ z, hA hz.1⟩
  have htu : γ t ∈ U := by
    rw [ht]
    change π (φ z) ∈ U
    rw [← hez]
    exact (e ⟨φ z, hA hz.1⟩).property
  refine ⟨t, htu, ?_⟩
  change physicalValue e y₀ (γ t) = φ z
  rw [physicalValue, dite_eq_left htu]
  have heq : (⟨γ t, htu⟩ : U) = e ⟨φ z, hA hz.1⟩ :=
    Subtype.ext (ht.trans hez.symm)
  rw [heq, e.symm_apply_apply]

 theorem compact_chart_length_le_occupation (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) {A : Set ℂ} (hA : MapsTo φ A G)
    (j : Y → ℂ) (hj : ∀ z ∈ A, j (φ z) = z)
    (B : ℝ≥0) (hB : LipschitzOnWith B j (φ '' A))
    (hφA : MeasurableSet (φ '' A)) (γ : FinitePhysicalPath e y₀) :
    (μH[1] : Measure ℂ) (A ∩ (π ∘ φ) ⁻¹' range γ.val) ≤
      (B : ℝ≥0∞) * physicalOccupationCode e y₀ γ.val (φ '' A) := by
  let E := A ∩ (π ∘ φ) ⁻¹' range γ.val
  have hEA : E ⊆ A := inter_subset_left
  have hid : j '' (φ '' E) = E := by
    ext w
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rwa [hj z (hEA hz)]
    · intro hw
      exact ⟨φ w, ⟨w, hw, rfl⟩, hj w (hEA hw)⟩
  calc
    (μH[1] : Measure ℂ) E = (μH[1] : Measure ℂ) (j '' (φ '' E)) := congrArg _ hid.symm
    _ ≤ (B : ℝ≥0∞) * (μH[1] : Measure Y) (φ '' E) := by
      simpa only [ENNReal.rpow_one] using
        (hB.mono (image_mono hEA)).hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1)
    _ ≤ (B : ℝ≥0∞) * physicalOccupationCode e y₀ γ.val (φ '' A) := by
      apply mul_le_mul' le_rfl
      rw [physicalOccupationCode_eq e y₀ γ]
      have hsub := physical_chart_image_subset e y₀ π he φ hA γ.val
      calc
        (μH[1] : Measure Y) (φ '' E) ≤ (μH[1] : Measure Y)
            ((φ '' A) ∩ ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U))) :=
          measure_mono (subset_inter (image_mono hEA) hsub)
        _ = ((μH[1] : Measure Y).restrict
            ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U))) (φ '' A) :=
          (Measure.restrict_apply hφA).symm
        _ ≤ _ := physical_image_hausdorff_le_occupation e hU y₀ γ _

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

 theorem mean_compactChartFiberCount_le_occupation
    (hcoarea : PlanarLipschitzFiberCoarea)
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) (hφ : Continuous φ) {A : Set ℂ} (hA : IsCompact A) (hAG : MapsTo φ A G)
    (j : Y → ℂ) (hj : ∀ z ∈ A, j (φ z) = z)
    (B : ℝ≥0) (hB : LipschitzOnWith B j (φ '' A))
    (K : Set C(PathTime, X)) (hK : ∀ γ ∈ K, Injective γ)
    (η : ProbabilityMeasure K)
    (hfinite : ∀ γ ∈ K, physicalDomainLength e y₀ γ < ∞)
    (L : ℝ≥0) (f : ℂ → ℝ) (hf : LipschitzWith L f) :
    (∫⁻ y, ∫⁻ γ : K, pathImageCount ((π ∘ φ) '' (A ∩ f ⁻¹' {y})) γ.val
      ∂(η : Measure K)) ≤
      (L : ℝ≥0∞) * B * meanPhysicalOccupation e y₀ (η.map Subtype.val) (φ '' A) := by
  have hφA : MeasurableSet (φ '' A) := (hA.image hφ).measurableSet
  have hlen (γ : K) := compact_chart_length_le_occupation e hU y₀ π he φ hAG j hj B hB hφA
    ⟨γ.val, hfinite γ.val γ.property⟩
  have hfin (γ : K) : (μH[1] : Measure ℂ) (A ∩ (π ∘ φ) ⁻¹' range γ.val) < ∞ := by
    apply (hlen γ).trans_lt
    apply ENNReal.mul_lt_top ENNReal.coe_lt_top
    rw [physicalOccupationCode_eq e y₀ ⟨γ.val, hfinite γ.val γ.property⟩]
    exact lt_of_le_of_lt (measure_mono (subset_univ _))
      (by rw [dyadicPhysicalOccupation_univ]; exact hfinite γ.val γ.property)
  calc
    _ ≤ (L : ℝ≥0∞) * ∫⁻ γ : K, (μH[1] : Measure ℂ)
        (A ∩ (π ∘ φ) ⁻¹' range γ.val) ∂(η : Measure K) :=
      mean_compactPhysicalFiberCount_integral_le hcoarea (π ∘ φ) (hπ.comp hφ) hA K hK
        (η : Measure K) L f hf (Eventually.of_forall hfin)
    _ ≤ (L : ℝ≥0∞) * ∫⁻ γ : K,
        (B : ℝ≥0∞) * physicalOccupationCode e y₀ γ.val (φ '' A) ∂(η : Measure K) :=
      mul_le_mul' le_rfl (lintegral_mono hlen)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, mul_assoc,
        meanPhysicalOccupation_apply e hU y₀ _ hφA, ProbabilityMeasure.toMeasure_map,
        lintegral_map]
      · exact (Measure.measurable_coe hφA).comp (measurable_physicalOccupationCode e hU y₀)
      · exact measurable_subtype_coe

end CircleDomainRigidity

end

end OAI
