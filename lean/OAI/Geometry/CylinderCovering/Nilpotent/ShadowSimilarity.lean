import OAI.Geometry.CylinderCovering.Nilpotent.ShadowSimilarityDefinitions
import OAI.Geometry.CylinderCovering.Nilpotent.Similarity
import OAI.Geometry.RuledCovering.Main

namespace OAI

noncomputable section
open Set MeasureTheory RuledApproximation
open scoped InnerProductSpace
namespace CylinderCovering.Nilpotent

private lemma inner_coordinates (u z : Space) :
    inner ℝ u z = u 0 * z 0 + u 1 * z 1 + u 2 * z 2 := by
  calc
    inner ℝ u z = inner ℝ (vec3 (u 0) (u 1) (u 2)) (vec3 (z 0) (z 1) (z 2)) := by
      congr 1 <;> ext i <;> fin_cases i <;> rfl
    _ = _ := inner_vec3 _ _ _ _ _ _

lemma centerDirection_inner (u z : Space) :
    inner ℝ (centerDirection u) (centerDirection z) = inner ℝ u z := by
  simp [inner_coordinates, centerDirection, vec3]

lemma centerDirection_norm (u : Space) : ‖centerDirection u‖ = ‖u‖ := by
  have hs : ‖centerDirection u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, centerDirection_inner, real_inner_self_eq_norm_sq]
  nlinarith [norm_nonneg (centerDirection u), norm_nonneg u]

lemma centerDirection_involutive (u : Space) : centerDirection (centerDirection u) = u := by
  ext i
  fin_cases i <;> simp [centerDirection, vec3]

lemma projection_centerMap (u z : Space) :
    TriangularCovering.projection (centerDirection u) (centerMap z) =
      -(inner ℝ (centerDirection u) (centerMap 0)) • centerDirection u +
        centerMap (TriangularCovering.projection u z) := by
  ext i
  fin_cases i <;>
    simp [TriangularCovering.projection, inner_coordinates, centerDirection, centerMap, vec3] <;>
    ring

lemma projection_centerMap_image (S : Set Space) (u : Space) :
    TriangularCovering.projection (centerDirection u) '' (centerMap '' S) =
      (fun z : Space => -(inner ℝ (centerDirection u) (centerMap 0)) • centerDirection u + z) ''
        (centerMap '' (TriangularCovering.projection u '' S)) := by
  simp only [image_image]
  congr 1
  funext z
  exact projection_centerMap u z

theorem centerMap_shadowArea (S : Set Space) (u : Space) :
    shadowArea (centerMap '' S) (centerDirection u) = shadowArea S u / 4 := by
  unfold shadowArea TriangularCovering.area
  rw [projection_centerMap_image]
  have hi : Isometry (fun z : Space =>
      -(inner ℝ (centerDirection u) (centerMap 0)) • centerDirection u + z) :=
    Isometry.of_dist_eq (by intro x y; simp)
  rw [hi.euclideanHausdorffMeasure_image]
  exact centerMap_area _

theorem shadowSimilarity : ShadowSimilarityStatement :=
  ⟨centerDirection_norm, centerMap_shadowArea⟩

end CylinderCovering.Nilpotent

end

end OAI
