import OAI.Geometry.NodalSets.Charts.SphereEnergyL2Map
import OAI.Geometry.NodalSets.Charts.SphereReferenceMeasureInvariance

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section
local instance sphereWeightedChartL2Measurable : MeasurableSpace Base := borel Base
local instance sphereWeightedChartL2Borel : BorelSpace Base := ⟨rfl⟩

theorem sphereWeightedMeasure_ae_iff (d : SphereEnergyData) (P : Base → Prop) :
    (∀ᵐ x ∂sphereWeightedMeasure d.density, P x) ↔ ∀ᵐ x ∂sphereReferenceMeasure, P x := by
  rw [sphereWeightedMeasure,ae_withDensity_iff d.continuous.measurable.ennreal_ofReal]
  simp only [ne_eq,ENNReal.ofReal_eq_zero,not_le.mpr (d.positive _),not_false_eq_true,true_implies]

theorem sphereWeightedMeasure_ae_chart_iff (d : SphereEnergyData) (p : Base) (P : Base → Prop) :
    (∀ᵐ x ∂sphereWeightedMeasure d.density, P x) ↔ ∀ᵐ y, P (sphereChartCoordMap p y) := by
  rw [sphereWeightedMeasure_ae_iff,sphereReferenceMeasure_eq_chart p,
    (sphereChartCoordMap_measurableEmbedding p).ae_map_iff]
  simp only [roundChartDensity_coord_eq]
  rw [ae_withDensity_iff roundCoordDensity_smooth.continuous.measurable.ennreal_ofReal]
  simp only [ne_eq,ENNReal.ofReal_eq_zero,not_le.mpr (roundCoordDensity_pos _),not_false_eq_true,true_implies]

theorem sphereWeightedMeasure_integrable_iff (d : SphereEnergyData) (F : Base → ℝ) :
    Integrable F (sphereWeightedMeasure d.density) ↔
      Integrable (fun x ↦ d.density x*F x) sphereReferenceMeasure := by
  rw [sphereWeightedMeasure,integrable_withDensity_iff_integrable_smul'
    d.continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (d.positive _).le,smul_eq_mul]

theorem sphereWeightedL2_test_pairing (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (h : Base → ℝ) (hh : Continuous h) :
    Integrable (fun x ↦ d.density x*f x*h x) sphereReferenceMeasure ∧
    inner ℝ f (sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) h hh) =
      ∫ x, d.density x*f x*h x ∂sphereReferenceMeasure := by
  let g := sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) h hh
  have hg : (g : Base → ℝ) =ᵐ[sphereWeightedMeasure d.density] h :=
    (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le) h hh).coeFn_toLp
  have he : (fun x ↦ inner ℝ (f x) (g x)) =ᵐ[sphereWeightedMeasure d.density]
      (fun x ↦ f x*h x) := by
    filter_upwards [hg] with x hx
    rw [hx]
    change h x*f x = f x*h x
    ring
  have hi : Integrable (fun x ↦ f x*h x) (sphereWeightedMeasure d.density) :=
    (L2.integrable_inner f g).congr he
  refine ⟨?_,?_⟩
  · simpa only [mul_assoc] using (sphereWeightedMeasure_integrable_iff d _).mp hi
  · change inner ℝ f g = _
    rw [L2.inner_def,integral_congr_ae he,
      sphereWeightedMeasure_integral d.density d.continuous (fun x ↦ (d.positive x).le)]
    simp only [mul_assoc]

theorem sphereWeightedL2_test_chart (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (h : Base → ℝ) (hh : Continuous h) (p : Base) :
    Integrable (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)*
      f (sphereChartCoordMap p y)*h (sphereChartCoordMap p y)) ∧
    inner ℝ f (sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) h hh) =
      ∫ y, roundCoordDensity y*d.density (sphereChartCoordMap p y)*
        f (sphereChartCoordMap p y)*h (sphereChartCoordMap p y) := by
  obtain ⟨hi,he⟩ := sphereWeightedL2_test_pairing d f h hh
  refine ⟨?_,?_⟩
  · simpa only [roundChartDensity_coord_eq,mul_assoc] using
      (sphereReferenceMeasure_integrable_chart p _).mp hi
  · rw [he,sphereReferenceMeasure_integral_chart p]
    simp only [roundChartDensity_coord_eq,mul_assoc]

end
end Yau.Target

end OAI
