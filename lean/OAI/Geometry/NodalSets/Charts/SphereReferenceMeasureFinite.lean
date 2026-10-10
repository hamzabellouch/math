import OAI.Geometry.NodalSets.Charts.SphereChartOpenMap
import OAI.Geometry.NodalSets.Charts.SphereReferenceMeasureInvariance

namespace OAI

namespace Yau.Target
open Manifold Set MeasureTheory Metric
open scoped ENNReal Topology
noncomputable section
local instance sphereReferenceMeasureFiniteLocal1 : MeasurableSpace Base := borel Base
local instance sphereReferenceMeasureFiniteLocal2 : BorelSpace Base := ⟨rfl⟩

lemma roundCoordDensity_le_one (x : Yau.Jets.Coord) : roundCoordDensity x ≤ 1 := by
  rw [roundCoordDensity,roundChartDensity_conformal]
  have h : 4/(‖seedCoordEquiv x‖^2+4) ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith [sq_nonneg (‖seedCoordEquiv x‖)])
  exact pow_le_one₀ (by positivity) h

lemma roundCoordMeasure_le_volume :
    volume.withDensity (fun x ↦ ENNReal.ofReal (roundCoordDensity x)) ≤ volume := by
  calc
    _ ≤ volume.withDensity 1 := withDensity_mono (Filter.Eventually.of_forall (fun x ↦ by
      simpa using ENNReal.ofReal_le_ofReal (roundCoordDensity_le_one x)))
    _ = _ := withDensity_one

lemma sphereReferenceMeasure_chart_ball_finite (p : Base) (r : ℝ) :
    sphereReferenceMeasure (sphereChartCoordMap p '' ball (0 : Yau.Jets.Coord) r) < ∞ := by
  rw [sphereReferenceMeasure_eq_chart p]
  simp only [roundChartDensity_coord_eq]
  rw [Measure.map_apply (sphereChartCoordMap_smooth p).continuous.measurable
    ((sphereChartCoordMap_isOpenMap p) _ isOpen_ball).measurableSet,
    Set.preimage_image_eq _ (sphereChartCoordMap_injective p)]
  exact lt_of_le_of_lt (roundCoordMeasure_le_volume _)
    (lt_of_le_of_lt (measure_mono ball_subset_closedBall) (isCompact_closedBall (0 : Yau.Jets.Coord) r).measure_lt_top)

lemma sphereReferenceMeasure_locallyFinite : IsLocallyFiniteMeasure sphereReferenceMeasure := by
  constructor
  intro p
  refine ⟨sphereChartCoordMap p '' ball (0 : Yau.Jets.Coord) 1,?_,sphereReferenceMeasure_chart_ball_finite p 1⟩
  apply ((sphereChartCoordMap_isOpenMap p) _ isOpen_ball).mem_nhds
  exact ⟨0,mem_ball_self (by norm_num),sphereChartCoordMap_zero p⟩

lemma sphereReferenceMeasure_finite : IsFiniteMeasure sphereReferenceMeasure := by
  let := sphereReferenceMeasure_locallyFinite
  infer_instance

lemma sphereReferenceMeasure_integrable_continuous (f : Base → ℝ) (hf : Continuous f) :
    Integrable f sphereReferenceMeasure := by
  let := sphereReferenceMeasure_finite
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

end
end Yau.Target

end OAI
