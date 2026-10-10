import OAI.Geometry.CylinderCovering.Radial.TetraGeometryDefinitions
import OAI.Geometry.CylinderCovering.Cubic.Similarity

namespace OAI

noncomputable section
namespace CylinderCovering.RadialPairedSweep
open Set MeasureTheory
open scoped InnerProductSpace

lemma tetrahedron_eq_neg_cubic : tetrahedron (Real.sqrt 2) =
    (fun z : Space => -z) '' Cubic.K4 := by
  ext z
  constructor
  · rintro ⟨x, y, t, hx, hy, rfl⟩
    refine ⟨TriangularCovering.point (-x) (-y) (-t), ?_, ?_⟩
    · refine ⟨-x, -y, -t, ?_, ?_, ?_, ?_, rfl⟩
      · linarith only [hy, abs_nonneg y]
      · linarith only [hx, abs_nonneg x]
      · simpa only [abs_neg, sub_neg_eq_add] using hx
      · simpa only [abs_neg, sub_eq_add_neg] using hy
    · ext i
      fin_cases i <;> simp [point, TriangularCovering.point, TriangularCovering.H]
  · rintro ⟨z, ⟨x, y, t, ht0, ht1, hx, hy, rfl⟩, rfl⟩
    refine ⟨-x, -y, -t, ?_, ?_, ?_⟩
    · simpa only [abs_neg, sub_eq_add_neg] using hx
    · simpa only [abs_neg, sub_neg_eq_add] using hy
    · ext i
      fin_cases i <;> simp [point, TriangularCovering.point, TriangularCovering.H]

lemma shadowArea_eq_cubic (u : Space) :
    shadowArea (tetrahedron (Real.sqrt 2)) u =
      TriangularCovering.area (TriangularCovering.projection u '' Cubic.K4) := by
  unfold shadowArea
  rw [tetrahedron_eq_neg_cubic]
  have himage : TriangularCovering.projection u '' ((fun z : Space => -z) '' Cubic.K4) =
      (fun z : Space => -z) '' (TriangularCovering.projection u '' Cubic.K4) := by
    simp only [Set.image_image]
    congr 1
    funext z
    simp only [TriangularCovering.projection, inner_neg_right, neg_smul]
    abel
  rw [himage]
  unfold TriangularCovering.area
  rw [isometry_neg.euclideanHausdorffMeasure_image]

lemma reference_shadow_lower (u : Space) (hu : ‖u‖ = 1) :
    4 * Real.sqrt 2 ≤ shadowArea (tetrahedron (Real.sqrt 2)) u := by
  rw [shadowArea_eq_cubic, Cubic.K4_shadow]
  exact mul_le_mul_of_nonneg_left (TriangularCovering.shadowArea_ge_H hu) (by norm_num)

lemma reference_minimum :
    minimumShadowArea (tetrahedron (Real.sqrt 2)) = 4 * Real.sqrt 2 := by
  unfold minimumShadowArea
  simp_rw [shadowArea_eq_cubic]
  exact Cubic.K4_projection_minimum

theorem reference_area : ReferenceAreaStatement :=
  ⟨reference_minimum, reference_shadow_lower⟩

lemma relativeCost_le_normalized_area {n : ℕ}
    (C : Fin n → TriangularCovering.TriCylinder) :
    triangularRelativeCost (tetrahedron (Real.sqrt 2)) C ≤
      TriangularCovering.totalArea C / (4 * Real.sqrt 2) := by
  unfold triangularRelativeCost TriangularCovering.totalArea
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  have hn : 0 ≤ TriangularCovering.area (C i).base := ENNReal.toReal_nonneg
  apply div_le_div_of_nonneg_left hn (by positivity)
  exact reference_shadow_lower (C i).axis (C i).unit_axis

theorem half_cost : HalfCostStatement := by
  intro n C hcost
  refine ⟨?_, ?_⟩
  · rw [reference_minimum]
    nlinarith only [hcost]
  · apply (relativeCost_le_normalized_area C).trans_lt
    apply (div_lt_iff₀ (by positivity : 0 < 4 * Real.sqrt 2)).mpr
    nlinarith only [hcost]

end CylinderCovering.RadialPairedSweep

end

end OAI
