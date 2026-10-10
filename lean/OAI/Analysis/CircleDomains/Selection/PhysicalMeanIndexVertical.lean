import OAI.Analysis.CircleDomains.Selection.MeanIndexHorizontalACL
import OAI.Analysis.CircleDomains.Selection.VerticalSliceCounts

namespace OAI

/-! Vertical absolute continuity and derivative bounds for the local mean
index. Coordinate interchange preserves physical area, and coarea bounds
the slices by the occupation density. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem physicalMeanIndex_vertical_ACL_derivative
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (A : Set C(PathTime, Sphere)) (hA : ∀ γ ∈ A, Injective γ)
    (η : ProbabilityMeasure A) (hfinite : ∀ γ ∈ A, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map Subtype.val) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {a b c d : ℝ} (I : Set ℝ) (hI : IsCompact I)
    (hac : a < c) (hcd : c ≤ d) (hdb : d < b)
    (hAG : MapsTo ((↑) : ℂ → Sphere) (planarSliceBox I (Icc a b)) G)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' planarSliceBox I (Icc a b)))
    (Ψ : ℂ → ℂ) (hΨ : ContinuousOn Ψ (planarSliceBox I (Icc a b)))
    (hpos : ∀ z ∈ planarSliceBox I (Icc a b), 0 ≤ (Ψ z).im)
    (hproj : ∀ z ∈ planarSliceBox I (Icc a b), diskRayProjection (Ψ z) = F (π (z : Sphere)))
    (v : ℂ → ℝ) (hv : ∀ z (hz : z ∈ planarSliceBox I (Icc a b)),
      v z = meanGeometricIndex hsch K hKS (η.map f) ⟨Ψ z, hpos z hz⟩)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪
      (fun z : ℂ => π (z : Sphere)) '' planarSliceBox I (Icc a b)))
    (hinj : InjOn (fun z : ℂ => F (π (z : Sphere))) (planarSliceBox I (Icc a b))) :
    ∀ᵐ x ∂volume.restrict I,
      AbsolutelyContinuousOnInterval (fun y => v ⟨x, y⟩) c d ∧
        (∀ᵐ y ∂volume.restrict (Icc c d), |deriv (fun t => v ⟨x, t⟩) y| ≤
          (sliceChartDensity B g ⟨x, y⟩).toReal) := by
  let Q : C(ℂ, Sphere) := ⟨fun z => π ((planarAxisSwap z : ℂ) : Sphere),
    (hπ.comp OnePoint.continuous_coe).comp continuous_planarAxisSwap⟩
  let ρ : ℂ → ℝ≥0∞ := sliceChartDensity B g
  have hρ : Measurable ρ := measurable_sliceChartDensity B hg
  have hswap : MapsTo planarAxisSwap (planarSliceBox (Icc a b) I)
      (planarSliceBox I (Icc a b)) := fun _ hz => ⟨hz.2, hz.1⟩
  have hQimage : Q '' planarSliceBox (Icc a b) I =
      (fun z : ℂ => π (z : Sphere)) '' planarSliceBox I (Icc a b) := by
    change ((fun z : ℂ => π (z : Sphere)) ∘ planarAxisSwap) '' _ = _
    rw [image_comp, planarAxisSwap_image_box]
  have hfin : (∫⁻ z in planarSliceBox I (Icc a b), ρ z) < ∞ := by
    let : IsFiniteMeasure (volume.restrict (planarSliceBox I (Icc a b))) :=
      isFiniteMeasure_restrict.mpr (isCompact_planarSliceBox hI isCompact_Icc).measure_lt_top.ne
    apply lintegral_lt_top_of_sq
    exact (lintegral_mono_set (subset_univ _)).trans_lt
      (by simpa only [Measure.restrict_univ] using sliceChartDensity_sq_integral_finite B g hg henergy)
  have hc := ae_sphericalVertical_rational_counts hcoarea e hU y₀ π hπ he hI
    hAG B hB A hA η hfinite g hg hocc henergy
  have hswapfin : (∫⁻ z in planarSliceBox (Icc a b) I, (ρ ∘ planarAxisSwap) z) < ∞ := by
    simpa only [Function.comp_apply, lintegral_planarAxisSwap_box (Icc a b) I measurableSet_Icc hI.measurableSet ρ hρ] using hfin
  have hr := meanIndex_horizontal_ACL_derivative hsch hsep A K hK hKS η F f hf hmap
    Q I hI.measurableSet hac hcd hdb (Ψ ∘ planarAxisSwap)
    (hΨ.comp continuous_planarAxisSwap.continuousOn hswap)
    (fun z hz => hpos _ (hswap hz)) (fun z hz => hproj _ (hswap hz))
    (v ∘ planarAxisSwap) (fun z hz => hv _ (hswap hz))
    (fun γ => by simpa only [hQimage] using hF γ) ?_
    (ρ ∘ planarAxisSwap) (hρ.comp continuous_planarAxisSwap.measurable)
    hswapfin ?_
  · simpa only [Function.comp_apply, planarAxisSwap, ρ] using hr
  · intro z hz w hw hzw
    apply planarAxisSwap_bijective.injective
    exact hinj (hswap hz) (hswap hw) hzw
  · filter_upwards [hc] with x hx
    intro p q hpq
    have hi := hx p q hpq
    change (∫⁻ γ : A, pathImageCount
      (((fun z : ℂ => π (z : Sphere)) ∘ planarAxisSwap) ''
        (planarSliceBox (Icc (p : ℝ) q) I ∩ Complex.im ⁻¹' {x})) γ.val ∂(η : Measure A)) ≤ _
    simpa only [image_comp, planarAxisSwap_image_horizontal_fiber,
      Function.comp_apply, planarAxisSwap, ρ] using hi

end CircleDomainRigidity

end

end OAI
