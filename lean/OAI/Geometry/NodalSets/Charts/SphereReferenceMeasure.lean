import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import OAI.Geometry.NodalSets.Charts.SphereChartTransition
import OAI.Geometry.NodalSets.Coefficients.RoundSupportedCorrection

namespace OAI

namespace Yau.Target
open Manifold Set MeasureTheory
open scoped ENNReal
noncomputable section

local instance sphereReferenceMeasureLocal1 : MeasurableSpace Base := borel Base
local instance sphereReferenceMeasureLocal2 : BorelSpace Base := ⟨rfl⟩

def sphereReferenceMeasure : Measure Base :=
  Measure.map seedSphereFromCoord
    (volume.withDensity (fun x ↦ ENNReal.ofReal (roundCoordDensity x)))

lemma seedSphereFromCoord_measurableEmbedding : MeasurableEmbedding seedSphereFromCoord :=
  seedSphereFromCoord_continuous.measurableEmbedding
    (Function.LeftInverse.injective seedSphereToCoord_from)

lemma sphereReferenceMeasure_integral (f : Base → ℝ) :
    (∫ p, f p ∂sphereReferenceMeasure) =
      ∫ x, roundCoordDensity x*f (seedSphereFromCoord x) := by
  rw [sphereReferenceMeasure,seedSphereFromCoord_measurableEmbedding.integral_map]
  rw [integral_withDensity_eq_integral_toReal_smul
    (roundCoordDensity_smooth.continuous.measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (roundCoordDensity_pos _).le,smul_eq_mul]

lemma sphereReferenceMeasure_integrable (f : Base → ℝ) :
    Integrable f sphereReferenceMeasure ↔
      Integrable (fun x ↦ roundCoordDensity x*f (seedSphereFromCoord x)) := by
  rw [sphereReferenceMeasure,seedSphereFromCoord_measurableEmbedding.integrable_map_iff,
    integrable_withDensity_iff_integrable_smul'
      (roundCoordDensity_smooth.continuous.measurable.ennreal_ofReal)
      (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (roundCoordDensity_pos _).le,smul_eq_mul,Function.comp_apply]

lemma sphereReferenceMeasure_chart_complement :
    sphereReferenceMeasure ((extChartAt (𝓡 4) seedPoint).sourceᶜ) = 0 := by
  rw [sphereReferenceMeasure,Measure.map_apply seedSphereFromCoord_continuous.measurable
    (isOpen_extChartAt_source seedPoint).measurableSet.compl]
  have he : seedSphereFromCoord ⁻¹' (extChartAt (𝓡 4) seedPoint).sourceᶜ = ∅ := by
    ext x
    simp only [mem_preimage,mem_compl_iff,mem_empty_iff_false,iff_false]
    exact not_not.mpr (seedSphereFromCoord_source x)
  rw [he,measure_empty]

lemma sphereReferenceMeasure_singleton (p : Base) : sphereReferenceMeasure {p} = 0 := by
  rw [sphereReferenceMeasure,Measure.map_apply seedSphereFromCoord_continuous.measurable
    (measurableSet_singleton p)]
  apply withDensity_absolutelyContinuous _ _
  have hs : (seedSphereFromCoord ⁻¹' {p}).Subsingleton :=
    Set.subsingleton_singleton.preimage seedSphereFromCoord_measurableEmbedding.injective
  exact hs.measure_zero volume

end
end Yau.Target

end OAI
