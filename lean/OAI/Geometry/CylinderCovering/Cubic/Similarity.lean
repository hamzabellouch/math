import OAI.Geometry.TriangularCovering.Main
import OAI.Geometry.CylinderCovering.Angular.CubicCoverDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace Pointwise
open TriangularCovering

namespace CubicSimilarity

lemma area_double_sub (S : Set Space) (t : Space) :
    area ((fun z : Space => (2 : ℝ) • z - t) '' S) = 4 * area S := by
  have hi : Isometry (fun z : Space => z - t) := by
    apply Isometry.of_dist_eq
    intro x y
    simp only [dist_eq_norm]
    congr 1
    abel
  have hs : (fun z : Space => (2 : ℝ) • z - t) '' S =
      (fun z : Space => z - t) '' ((2 : ℝ) • S) := by
    rw [← Set.image_smul, Set.image_image]
  unfold area
  rw [hs, hi.euclideanHausdorffMeasure_image,
    Measure.euclideanHausdorffMeasure_smul₀ 2 (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num [ENNReal.smul_def, ENNReal.toReal_mul]

lemma projection_double_sub (u z t : Space) :
    projection u ((2 : ℝ) • z - t) =
      (2 : ℝ) • projection u z - projection u t := by
  change projLinear u ((2 : ℝ) • z - t) =
    (2 : ℝ) • projLinear u z - projLinear u t
  rw [map_sub, map_smul]

lemma shadow_double_sub (u t : Space) :
    area (projection u '' ((fun z : Space => (2 : ℝ) • z - t) '' K)) =
      4 * shadowArea u := by
  have hs : projection u '' ((fun z : Space => (2 : ℝ) • z - t) '' K) =
      (fun z : Space => (2 : ℝ) • z - projection u t) '' (projection u '' K) := by
    simp only [Set.image_image]
    congr 1
    funext z
    exact projection_double_sub u z t
  rw [hs, area_double_sub]
  rfl

lemma double_sub_point (x y t : ℝ) :
    (2 : ℝ) • point x y t - point 0 0 1 = point (2*x) (2*y) (2*t-1) := by
  ext i
  fin_cases i <;> dsimp [point] <;> ring

end CubicSimilarity

namespace CylinderCovering.Cubic

lemma K4_eq_double_sub :
    K4 = (fun z : Space => (2 : ℝ) • z - point 0 0 1) '' K := by
  ext p
  constructor
  · rintro ⟨x, y, z, hz0, hz1, hx, hy, rfl⟩
    refine ⟨point (x / 2) (y / 2) ((z + 1) / 2), ?_, ?_⟩
    · refine ⟨x / 2, y / 2, (z + 1) / 2, by linarith, by linarith, ?_, ?_, rfl⟩
      · rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]
        linarith
      · rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]
        linarith
    · dsimp only
      rw [CubicSimilarity.double_sub_point]
      congr 1 <;> ring
  · rintro ⟨q, ⟨x, y, t, ht0, ht1, hx, hy, rfl⟩, rfl⟩
    dsimp only
    rw [CubicSimilarity.double_sub_point]
    refine ⟨2 * x, 2 * y, 2 * t - 1, by linarith, by linarith, ?_, ?_, rfl⟩
    · rw [abs_mul, show |(2 : ℝ)| = 2 by norm_num]
      linarith
    · rw [abs_mul, show |(2 : ℝ)| = 2 by norm_num]
      linarith

lemma K4_shadow (u : Space) :
    area (projection u '' K4) = 4 * shadowArea u := by
  rw [K4_eq_double_sub]
  exact CubicSimilarity.shadow_double_sub u (point 0 0 1)

theorem K4_projection_minimum :
    sInf {a : ℝ | ∃ u : Space, ‖u‖ = 1 ∧ a = area (projection u '' K4)} = 4 * H := by
  have hlo (u : Space) (hu : ‖u‖ = 1) : 4 * H ≤ area (projection u '' K4) := by
    rw [K4_shadow]
    exact mul_le_mul_of_nonneg_left (shadowArea_ge_H hu) (by norm_num)
  have heq : area (projection (tiltV 0 0 0) '' K4) = 4 * H := by
    rw [K4_shadow, xAxis_shadow]
  apply le_antisymm
  · apply csInf_le
    · exact ⟨4 * H, by rintro a ⟨u, hu, rfl⟩; exact hlo u hu⟩
    · exact ⟨tiltV 0 0 0, xAxis_unit, heq.symm⟩
  · apply le_csInf
    · exact ⟨4 * H, tiltV 0 0 0, xAxis_unit, heq.symm⟩
    · rintro a ⟨u, hu, rfl⟩
      exact hlo u hu

lemma K4_compact : IsCompact K4 := by
  rw [K4_eq_double_sub]
  exact K_compact.image (by fun_prop)

lemma K4_edge_length {i j : Fin 4} (hij : i ≠ j) :
    dist ((2 : ℝ) • tetraVertices i - point 0 0 1)
      ((2 : ℝ) • tetraVertices j - point 0 0 1) = 4 := by
  rw [dist_sub_right, dist_eq_norm, ← smul_sub, norm_smul, ← dist_eq_norm,
    tetra_edge_length hij]
  norm_num

end CylinderCovering.Cubic

end

end OAI
