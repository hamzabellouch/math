import OAI.MeasureTheory.Falconer.Angular.GnomonicConeVolume

namespace OAI

/-! # The published gnomonic surface identity proved from Euclidean cone volume -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal Pointwise

theorem gnomonic_sphere_image {n : ℕ} {A : Set (Space n)} (hA : MeasurableSet A) :
    sphereMeasure (n+1) (gnomonicChart '' A) =
      ((volume : Measure (Space n)).withDensity (fun x => ENNReal.ofReal (gnomonicDensity x))) A := by
  have hchart : MeasurableSet (gnomonicChart '' A) :=
    (gnomonicChart_measurableEmbedding n).measurableSet_image.mpr hA
  have hd : (0:ℝ) < ((n+1:ℕ):ℝ) := by positivity
  rw [sphereMeasure,Measure.toSphere_apply' _ hchart]
  change (Module.finrank ℝ (Space (n+1)) : ℝ≥0∞)*volume (gnomonicCone A) = _
  rw [show Module.finrank ℝ (Space (n+1)) = n+1 by simp [Space],gnomonicCone_volume hA,
    withDensity_apply _ hA]
  rw [← ENNReal.ofReal_natCast,← lintegral_const_mul _
    (((gnomonicDensity_continuous n).measurable.div_const _).ennreal_ofReal)]
  apply lintegral_congr_ae
  filter_upwards with x
  rw [← ENNReal.ofReal_mul hd.le]
  congr 1
  field_simp

theorem published_gnomonic_surface : PublishedGnomonicSurface := by
  intro n _hn
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (gnomonicChart_continuous n).measurable hB]
  have hA : MeasurableSet (gnomonicChart ⁻¹' B) := hB.preimage (gnomonicChart_continuous n).measurable
  rw [← gnomonic_sphere_image hA,Set.image_preimage_eq_inter_range,gnomonicChart_range,
    Measure.restrict_apply hB]

end Falconer

end OAI
