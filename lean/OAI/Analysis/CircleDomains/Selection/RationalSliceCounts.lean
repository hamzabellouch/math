import OAI.Analysis.CircleDomains.Topology.SphericalSlicePointwise

namespace OAI

/-! A common full-measure set for every rational horizontal interval. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem ae_sphericalHorizontal_rational_counts
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    {I J : Set ℝ} (hJ : IsCompact J)
    (hAG : MapsTo ((↑) : ℂ → Sphere) (planarSliceBox I J) G)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' planarSliceBox I J))
    (K : Set C(PathTime, Sphere)) (hK : ∀ γ ∈ K, Injective γ)
    (η : ProbabilityMeasure K) (hfinite : ∀ γ ∈ K, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map Subtype.val) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) :
    ∀ᵐ y ∂volume, ∀ p q : ℚ, Icc (p : ℝ) q ⊆ I →
      (∫⁻ γ : K, pathImageCount
        ((fun z : ℂ => π (z : Sphere)) ''
          (planarSliceBox (Icc (p : ℝ) q) J ∩ Complex.im ⁻¹' {y})) γ.val ∂(η : Measure K)) ≤
        ∫⁻ x in Icc (p : ℝ) q, sliceChartDensity B g ⟨x, y⟩ := by
  refine ae_all_iff.mpr fun p => ae_all_iff.mpr fun q => ?_
  by_cases hpq : Icc (p : ℝ) q ⊆ I
  · have hsub := planarSliceBox_mono hpq (Subset.rfl : J ⊆ J)
    exact (ae_sphericalHorizontalCount_le_density hcoarea e hU y₀ π hπ he
      isCompact_Icc hJ (hAG.mono_left hsub) B (hB.mono (image_mono hsub))
      K hK η hfinite g hg hocc henergy).mono fun _ h _ => h
  · exact Eventually.of_forall fun _ h => (hpq h).elim

end CircleDomainRigidity

end

end OAI
