import OAI.Analysis.CircleDomains.Selection.MeanIndexHorizontalACL
import OAI.Analysis.CircleDomains.Selection.RationalSliceCounts

namespace OAI

/-! Horizontal absolute continuity and derivative bounds for the local
mean index, from physical coarea and its occupation density. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem physicalMeanIndex_horizontal_ACL_derivative
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
    {a b c d : ℝ} (J : Set ℝ) (hJ : IsCompact J)
    (hac : a < c) (hcd : c ≤ d) (hdb : d < b)
    (hAG : MapsTo ((↑) : ℂ → Sphere) (planarSliceBox (Icc a b) J) G)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' planarSliceBox (Icc a b) J))
    (Ψ : ℂ → ℂ) (hΨ : ContinuousOn Ψ (planarSliceBox (Icc a b) J))
    (hpos : ∀ z ∈ planarSliceBox (Icc a b) J, 0 ≤ (Ψ z).im)
    (hproj : ∀ z ∈ planarSliceBox (Icc a b) J, diskRayProjection (Ψ z) = F (π (z : Sphere)))
    (v : ℂ → ℝ) (hv : ∀ z (hz : z ∈ planarSliceBox (Icc a b) J),
      v z = meanGeometricIndex hsch K hKS (η.map f) ⟨Ψ z, hpos z hz⟩)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪
      (fun z : ℂ => π (z : Sphere)) '' planarSliceBox (Icc a b) J))
    (hinj : InjOn (fun z : ℂ => F (π (z : Sphere))) (planarSliceBox (Icc a b) J)) :
    ∀ᵐ y ∂volume.restrict J,
      AbsolutelyContinuousOnInterval (fun x => v ⟨x, y⟩) c d ∧
        (∀ᵐ x ∂volume.restrict (Icc c d), |deriv (fun t => v ⟨t, y⟩) x| ≤
          (sliceChartDensity B g ⟨x, y⟩).toReal) := by
  let Q : C(ℂ, Sphere) := ⟨fun z => π (z : Sphere), hπ.comp OnePoint.continuous_coe⟩
  have hρ := measurable_sliceChartDensity B hg
  have hrect := isCompact_planarSliceBox (I := Icc a b) isCompact_Icc hJ
  have hfin : (∫⁻ z in planarSliceBox (Icc a b) J, sliceChartDensity B g z) < ∞ := by
    let : IsFiniteMeasure (volume.restrict (planarSliceBox (Icc a b) J)) :=
      isFiniteMeasure_restrict.mpr hrect.measure_lt_top.ne
    apply lintegral_lt_top_of_sq
    exact (lintegral_mono_set (subset_univ _)).trans_lt
      (by simpa only [Measure.restrict_univ] using sliceChartDensity_sq_integral_finite B g hg henergy)
  exact meanIndex_horizontal_ACL_derivative hsch hsep A K hK hKS η F f hf hmap
    Q J hJ.measurableSet hac hcd hdb Ψ hΨ hpos hproj v hv hF hinj
    (sliceChartDensity B g) hρ hfin
    (ae_sphericalHorizontal_rational_counts hcoarea e hU y₀ π hπ he hJ hAG B hB
      A hA η hfinite g hg hocc henergy)

end CircleDomainRigidity

end

end OAI
