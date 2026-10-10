import OAI.Geometry.NodalSets.Charts.SphereMeasureChartGeometry
import OAI.Geometry.NodalSets.Charts.SphereReferenceMeasure

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section
local instance sphereReferenceMeasureInvarianceLocal1 : MeasurableSpace Base := borel Base
local instance sphereReferenceMeasureInvarianceLocal2 : BorelSpace Base := ⟨rfl⟩

lemma sphereChartCoordMap_measurableEmbedding (p : Base) : MeasurableEmbedding (sphereChartCoordMap p) :=
  (sphereChartCoordMap_smooth p).continuous.measurableEmbedding (sphereChartCoordMap_injective p)

lemma roundChartDensity_coord_eq (p : Base) (x : Yau.Jets.Coord) :
    roundChartDensity p (seedCoordEquiv x) = roundCoordDensity x := by
  simp only [roundCoordDensity,roundChartDensity_conformal]

lemma sphereReferenceMeasure_lintegral_chart_change (p q : Base) (f : Base → ℝ≥0∞) :
    (∫⁻ x, ENNReal.ofReal (roundCoordDensity x)*f (sphereChartCoordMap p x)) =
      ∫⁻ x, ENNReal.ofReal (roundCoordDensity x)*f (sphereChartCoordMap q x) := by
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (sphereChartTransitionDomain_open p q).measurableSet
    (fun x hx ↦ (sphereChartTransition_hasFDeriv p q hx).hasFDerivWithinAt)
    (sphereChartTransition_injOn p q)
    (fun y ↦ ENNReal.ofReal (roundCoordDensity y)*f (sphereChartCoordMap q y))
  rw [sphereChartTransition_image_domain] at h
  have hp : volume.restrict (sphereChartTransitionDomain p q) = volume :=
    Measure.restrict_eq_self_of_ae_mem (sphereChartTransitionDomain_ae p q)
  have hq : volume.restrict (sphereChartTransitionDomain q p) = volume :=
    Measure.restrict_eq_self_of_ae_mem (sphereChartTransitionDomain_ae q p)
  rw [hp,hq] at h
  rw [h]
  apply lintegral_congr_ae
  filter_upwards [sphereChartTransitionDomain_ae p q] with x hx
  have hd := sphereChartTransition_round_density p q hx
  simp only [roundChartDensity_coord_eq,jacobian_det_eq] at hd
  rw [sphereChartTransition_point p q hx,hd,ENNReal.ofReal_mul (abs_nonneg _),mul_assoc]

theorem sphereReferenceMeasure_eq_chart (p : Base) :
    sphereReferenceMeasure = Measure.map (sphereChartCoordMap p)
      (volume.withDensity (fun x ↦ ENNReal.ofReal (roundChartDensity p (seedCoordEquiv x)))) := by
  apply Measure.ext_of_lintegral
  intro f hf
  simp only [sphereReferenceMeasure,roundChartDensity_coord_eq]
  rw [seedSphereFromCoord_measurableEmbedding.lintegral_map,
    (sphereChartCoordMap_measurableEmbedding p).lintegral_map,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      roundCoordDensity_smooth.continuous.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)),
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      roundCoordDensity_smooth.continuous.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  exact sphereReferenceMeasure_lintegral_chart_change seedPoint p f

lemma sphereReferenceMeasure_integral_chart (p : Base) (f : Base → ℝ) :
    (∫ z, f z ∂sphereReferenceMeasure) =
      ∫ x, roundChartDensity p (seedCoordEquiv x)*f (sphereChartCoordMap p x) := by
  rw [sphereReferenceMeasure_eq_chart p,(sphereChartCoordMap_measurableEmbedding p).integral_map]
  simp only [roundChartDensity_coord_eq]
  rw [integral_withDensity_eq_integral_toReal_smul
    roundCoordDensity_smooth.continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (roundCoordDensity_pos _).le,smul_eq_mul]

lemma sphereReferenceMeasure_integrable_chart (p : Base) (f : Base → ℝ) :
    Integrable f sphereReferenceMeasure ↔
      Integrable (fun x ↦ roundChartDensity p (seedCoordEquiv x)*f (sphereChartCoordMap p x)) := by
  rw [sphereReferenceMeasure_eq_chart p,(sphereChartCoordMap_measurableEmbedding p).integrable_map_iff]
  simp only [roundChartDensity_coord_eq]
  rw [integrable_withDensity_iff_integrable_smul'
    roundCoordDensity_smooth.continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (roundCoordDensity_pos _).le,smul_eq_mul,Function.comp_apply]

end
end Yau.Target

end OAI
