import OAI.Analysis.CircleDomains.Topology.SphericalSlicePointwise
import OAI.Analysis.CircleDomains.Topology.PlanarAxisSwap

namespace OAI

/-! Vertical physical slice bounds from planar coarea, with the
coordinate axes interchanged. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem ae_sphericalVerticalCount_le_density
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    {I J : Set ℝ} (hI : IsCompact I) (hJ : IsCompact J)
    (hAG : MapsTo ((↑) : ℂ → Sphere) (planarSliceBox I J) G)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' planarSliceBox I J))
    (K : Set C(PathTime, Sphere)) (hK : ∀ γ ∈ K, Injective γ)
    (η : ProbabilityMeasure K) (hfinite : ∀ γ ∈ K, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map Subtype.val) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) :
    ∀ᵐ x ∂volume, (∫⁻ γ : K, pathImageCount
      ((fun z : ℂ => π (z : Sphere)) ''
        (planarSliceBox I J ∩ Complex.re ⁻¹' {x})) γ.val ∂(η : Measure K)) ≤
      ∫⁻ y in J, sliceChartDensity B g ⟨x, y⟩ := by
  let Q : ℂ → Sphere := fun z => π (z : Sphere)
  let ρ : ℂ → ℝ≥0∞ := sliceChartDensity B g
  have hρ : Measurable ρ := measurable_sliceChartDensity B hg
  have hfin : (∫⁻ z in planarSliceBox I J, ρ z) < ∞ := by
    let : IsFiniteMeasure (volume.restrict (planarSliceBox I J)) :=
      isFiniteMeasure_restrict.mpr (isCompact_planarSliceBox hI hJ).measure_lt_top.ne
    apply lintegral_lt_top_of_sq
    exact (lintegral_mono_set (subset_univ _)).trans_lt
      (by simpa only [Measure.restrict_univ] using sliceChartDensity_sq_integral_finite B g hg henergy)
  have hswapfin : (∫⁻ z in planarSliceBox J I, (ρ ∘ planarAxisSwap) z) < ∞ := by
    simpa only [Function.comp_apply, lintegral_planarAxisSwap_box J I hJ.measurableSet hI.measurableSet ρ hρ] using hfin
  have hswap := ae_meanSliceCount_le (Q ∘ planarAxisSwap)
    ((hπ.comp OnePoint.continuous_coe).comp continuous_planarAxisSwap)
    K hK (η : Measure K) hJ hI (ρ ∘ planarAxisSwap)
    (hρ.comp continuous_planarAxisSwap.measurable)
    hswapfin ?_
  · filter_upwards [hswap] with x hx
    simpa only [image_comp, planarAxisSwap_image_horizontal_fiber,
      Function.comp_apply, planarAxisSwap, Q, ρ] using hx
  · intro C hC hCI
    have hsub : planarSliceBox C J ⊆ planarSliceBox I J :=
      planarSliceBox_mono hCI Subset.rfl
    have hb := mean_sphericalSliceCount_le_density hcoarea e hU y₀ π hπ he
      (isCompact_planarSliceBox hC hJ) (hAG.mono_left hsub) B
      (hB.mono (image_mono hsub)) K hK η hfinite g hg hocc
      1 Complex.re RCLike.lipschitzWith_re
    change (∫⁻ y, ∫⁻ γ : K, pathImageCount
      (((fun z : ℂ => π (z : Sphere)) ∘ planarAxisSwap) ''
        (planarSliceBox J C ∩ Complex.im ⁻¹' {y})) γ.val ∂(η : Measure K)) ≤ _
    simp only [image_comp, planarAxisSwap_image_horizontal_fiber]
    simpa only [Function.comp_apply, lintegral_planarAxisSwap_box J C hJ.measurableSet
        hC.measurableSet ρ hρ, ENNReal.coe_one, one_mul, ρ] using hb

 theorem ae_sphericalVertical_rational_counts
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    {I J : Set ℝ} (hI : IsCompact I)
    (hAG : MapsTo ((↑) : ℂ → Sphere) (planarSliceBox I J) G)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' planarSliceBox I J))
    (K : Set C(PathTime, Sphere)) (hK : ∀ γ ∈ K, Injective γ)
    (η : ProbabilityMeasure K) (hfinite : ∀ γ ∈ K, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map Subtype.val) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) :
    ∀ᵐ x ∂volume, ∀ p q : ℚ, Icc (p : ℝ) q ⊆ J →
      (∫⁻ γ : K, pathImageCount
        ((fun z : ℂ => π (z : Sphere)) ''
          (planarSliceBox I (Icc (p : ℝ) q) ∩ Complex.re ⁻¹' {x})) γ.val ∂(η : Measure K)) ≤
        ∫⁻ y in Icc (p : ℝ) q, sliceChartDensity B g ⟨x, y⟩ := by
  refine ae_all_iff.mpr fun p => ae_all_iff.mpr fun q => ?_
  by_cases hpq : Icc (p : ℝ) q ⊆ J
  · have hsub := planarSliceBox_mono (Subset.rfl : I ⊆ I) hpq
    exact (ae_sphericalVerticalCount_le_density hcoarea e hU y₀ π hπ he
      hI isCompact_Icc (hAG.mono_left hsub) B (hB.mono (image_mono hsub))
      K hK η hfinite g hg hocc henergy).mono fun _ h _ => h
  · exact Eventually.of_forall fun _ h => (hpq h).elim

end CircleDomainRigidity

end

end OAI
