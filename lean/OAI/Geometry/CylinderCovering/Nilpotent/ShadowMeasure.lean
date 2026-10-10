import OAI.Geometry.CylinderCovering.Nilpotent.ShadowSimilarity

namespace OAI

noncomputable section
open Set MeasureTheory RuledApproximation
open scoped Pointwise
namespace CylinderCovering.Nilpotent

theorem centerMap_hausdorffMeasure (S : Set Space) :
    Measure.euclideanHausdorffMeasure 2 (centerMap '' S) =
      (1 / 4 : NNReal) • Measure.euclideanHausdorffMeasure 2 S := by
  have hiso : Isometry (fun z : Space => (2 : ℝ) • centerMap z) := by
    apply isometry_iff_dist_eq.mpr
    intro x y
    rw [dist_smul₀, centerMap_dist]
    norm_num
    ring
  have himage : centerMap '' S =
      (1 / 2 : ℝ) • ((fun z : Space => (2 : ℝ) • centerMap z) '' S) := by
    rw [← image_smul, image_image]
    congr 1
    funext z
    simp [smul_smul]
  rw [himage, Measure.euclideanHausdorffMeasure_smul₀ 2
    (by norm_num : (1 / 2 : ℝ) ≠ 0), hiso.euclideanHausdorffMeasure_image]
  norm_num

theorem centerMap_shadowMeasure (S : Set Space) (u : Space) :
    Measure.euclideanHausdorffMeasure 2
        (TriangularCovering.projection (centerDirection u) '' (centerMap '' S)) =
      (1 / 4 : NNReal) • Measure.euclideanHausdorffMeasure 2
        (TriangularCovering.projection u '' S) := by
  rw [projection_centerMap_image]
  have hi : Isometry (fun z : Space =>
      -(inner ℝ (centerDirection u) (centerMap 0)) • centerDirection u + z) :=
    Isometry.of_dist_eq (by intro x y; simp)
  rw [hi.euclideanHausdorffMeasure_image]
  exact centerMap_hausdorffMeasure _

end CylinderCovering.Nilpotent

end

end OAI
