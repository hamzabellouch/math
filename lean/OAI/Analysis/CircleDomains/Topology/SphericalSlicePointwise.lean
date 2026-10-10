import OAI.Analysis.CircleDomains.Probability.SphericalSliceDensity
import OAI.Analysis.CircleDomains.Selection.MeanSlicePointwise
import OAI.Analysis.CircleDomains.Sobolev.LocalDensityIntegrability

namespace OAI

/-! The almost-everywhere physical line estimate for the compact simple-arc
law. The only coarea hypothesis is the cited plane-to-line theorem. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem ae_sphericalHorizontalCount_le_density
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
    ∀ᵐ y ∂volume, (∫⁻ γ : K, pathImageCount
      ((fun z : ℂ => π (z : Sphere)) ''
        (planarSliceBox I J ∩ Complex.im ⁻¹' {y})) γ.val ∂(η : Measure K)) ≤
      ∫⁻ x in I, sliceChartDensity B g ⟨x, y⟩ := by
  have hA := isCompact_planarSliceBox hI hJ
  have hρ := measurable_sliceChartDensity B hg
  have hfin : (∫⁻ z in planarSliceBox I J, sliceChartDensity B g z) < ∞ := by
    let : IsFiniteMeasure (volume.restrict (planarSliceBox I J)) :=
      isFiniteMeasure_restrict.mpr hA.measure_lt_top.ne
    apply lintegral_lt_top_of_sq
    exact (lintegral_mono_set (subset_univ _)).trans_lt
      (by simpa only [Measure.restrict_univ] using sliceChartDensity_sq_integral_finite B g hg henergy)
  apply ae_meanSliceCount_le (fun z : ℂ => π (z : Sphere))
    (hπ.comp OnePoint.continuous_coe) K hK (η : Measure K) hI hJ _ hρ hfin
  intro C hC hCJ
  have hsub : planarSliceBox I C ⊆ planarSliceBox I J := planarSliceBox_mono Subset.rfl hCJ
  have hb := mean_sphericalSliceCount_le_density hcoarea e hU y₀ π hπ he
    (isCompact_planarSliceBox hI hC) (hAG.mono_left hsub) B (hB.mono (image_mono hsub))
    K hK η hfinite g hg hocc 1 Complex.im RCLike.lipschitzWith_im
  simpa only [ENNReal.coe_one, one_mul] using hb

end CircleDomainRigidity

end

end OAI
