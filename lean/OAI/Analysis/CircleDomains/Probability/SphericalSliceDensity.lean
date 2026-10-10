import OAI.Analysis.CircleDomains.Probability.PhysicalSliceOccupation
import OAI.Analysis.CircleDomains.Topology.SphereSliceChart

namespace OAI

/-! The physical occupation density gives a square-integrable planar
slice density in every finite inverse-chart neighborhood. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal Classical

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem sphericalArea_setLIntegral_coe {A : Set ℂ} (hA : MeasurableSet A)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ p in ((↑) : ℂ → Sphere) '' A, g p ∂sphericalArea) =
      ∫⁻ z in A, ENNReal.ofReal (sphericalAreaDensity z) * g (z : Sphere) := by
  have hm : MeasurableSet (((↑) : ℂ → Sphere) '' A) :=
    OnePoint.isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr hA
  rw [← lintegral_indicator hm, lintegral_sphericalArea _ (hg.indicator hm),
    ← lintegral_indicator hA]
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ A <;> simp [hz]

 def sliceChartDensity (B : ℝ≥0) (g : Sphere → ℝ≥0∞) (z : ℂ) : ℝ≥0∞ :=
  (B : ℝ≥0∞) * ENNReal.ofReal (sphericalAreaDensity z) * g (z : Sphere)

 theorem measurable_sliceChartDensity (B : ℝ≥0) {g : Sphere → ℝ≥0∞} (hg : Measurable g) :
    Measurable (sliceChartDensity B g) :=
  (measurable_const.mul continuous_sphericalAreaDensity.measurable.ennreal_ofReal).mul
    (hg.comp OnePoint.continuous_coe.measurable)

 theorem sliceChartDensity_sq_integral_le (B : ℝ≥0) (g : Sphere → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z, sliceChartDensity B g z ^ 2) ≤
      (4 * (B : ℝ≥0∞) ^ 2) * ∫⁻ p, g p ^ 2 ∂sphericalArea := by
  rw [lintegral_sphericalArea _ (hg.pow_const 2)]
  calc
    _ ≤ ∫⁻ z : ℂ, (4 * (B : ℝ≥0∞) ^ 2) *
        (ENNReal.ofReal (sphericalAreaDensity z) * g (z : Sphere) ^ 2) := by
      apply lintegral_mono
      intro z
      have ha : ENNReal.ofReal (sphericalAreaDensity z) ≤ 4 :=
        (ENNReal.ofReal_le_ofReal (sphericalAreaDensity_le_four z)).trans_eq (by norm_num)
      calc
        sliceChartDensity B g z ^ 2 = (B : ℝ≥0∞) ^ 2 *
            ((ENNReal.ofReal (sphericalAreaDensity z)) ^ 2 * g (z : Sphere) ^ 2) := by
          simp only [sliceChartDensity, mul_pow, mul_assoc]
        _ ≤ (B : ℝ≥0∞) ^ 2 * ((4 * ENNReal.ofReal (sphericalAreaDensity z)) *
            g (z : Sphere) ^ 2) := by
          have ha2 : ENNReal.ofReal (sphericalAreaDensity z) ^ 2 ≤
              4 * ENNReal.ofReal (sphericalAreaDensity z) := by
            simpa only [pow_two] using
              mul_le_mul' ha (le_refl (ENNReal.ofReal (sphericalAreaDensity z)))
          exact mul_le_mul' le_rfl (mul_le_mul' ha2 le_rfl)
        _ = _ := by ring
    _ = _ := lintegral_const_mul' _ _ (by finiteness)

 theorem sliceChartDensity_sq_integral_finite (B : ℝ≥0) (g : Sphere → ℝ≥0∞)
    (hg : Measurable g) (hfin : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) :
    (∫⁻ z, sliceChartDensity B g z ^ 2) < ∞ :=
  (sliceChartDensity_sq_integral_le B g hg).trans_lt
    (ENNReal.mul_lt_top (by finiteness) hfin)

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem mean_sphericalSliceCount_le_density
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    {A : Set ℂ} (hA : IsCompact A) (hAG : MapsTo ((↑) : ℂ → Sphere) A G)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord (((↑) : ℂ → Sphere) '' A))
    (K : Set C(PathTime, Sphere)) (hK : ∀ γ ∈ K, Injective γ)
    (η : ProbabilityMeasure K) (hfinite : ∀ γ ∈ K, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map Subtype.val) = sphericalArea.withDensity g)
    (L : ℝ≥0) (f : ℂ → ℝ) (hf : LipschitzWith L f) :
    (∫⁻ y, ∫⁻ γ : K, pathImageCount
      ((fun z : ℂ => π (z : Sphere)) '' (A ∩ f ⁻¹' {y})) γ.val ∂(η : Measure K)) ≤
      (L : ℝ≥0∞) * ∫⁻ z in A, sliceChartDensity B g z := by
  have hm := (hA.image OnePoint.continuous_coe).measurableSet
  have hb := mean_compactChartFiberCount_le_occupation hcoarea e hU y₀ π hπ he
    ((↑) : ℂ → Sphere) OnePoint.continuous_coe hA hAG finiteCoord
    (fun z _ => finiteCoord_coe z) B hB K hK η hfinite L f hf
  rw [hocc, withDensity_apply _ hm, sphericalArea_setLIntegral_coe hA.measurableSet g hg] at hb
  simpa only [Function.comp_def, sliceChartDensity, mul_assoc,
    lintegral_const_mul' _ _ ENNReal.coe_ne_top] using hb

end CircleDomainRigidity

end

end OAI
