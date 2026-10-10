import OAI.Geometry.CylinderCovering.Rational.ConstructionDefinitions
import OAI.Geometry.CylinderCovering.Rational.Realization
import OAI.Geometry.CylinderCovering.Convexity.CylinderSimilarity
import OAI.Geometry.TriangularCovering.Main

namespace OAI

noncomputable section
open Set

namespace SlopeRational

def centeringIsometry : Space ≃ₗᵢ[ℝ] Space where
  toFun z := RuledApproximation.vec3 (z 1) (z 0) (z 2)
  invFun z := RuledApproximation.vec3 (z 1) (z 0) (z 2)
  left_inv z := by ext i; fin_cases i <;> simp [RuledApproximation.vec3]
  right_inv z := by ext i; fin_cases i <;> simp [RuledApproximation.vec3]
  map_add' z w := by ext i; fin_cases i <;> simp [RuledApproximation.vec3]
  map_smul' c z := by ext i; fin_cases i <;> simp [RuledApproximation.vec3]
  norm_map' z := by
    change ‖RuledApproximation.vec3 (z 1) (z 0) (z 2)‖ = ‖z‖
    have hsq : ‖RuledApproximation.vec3 (z 1) (z 0) (z 2)‖ ^ 2 = ‖z‖ ^ 2 := by
      simp [EuclideanSpace.norm_sq_eq, RuledApproximation.vec3, Fin.sum_univ_succ]
      ring
    nlinarith [norm_nonneg (RuledApproximation.vec3 (z 1) (z 0) (z 2)), norm_nonneg z]

def centeringTranslation : Space := RuledApproximation.vec3 0 0 (-physicalScale / 2)

lemma twice_physicalScale : 2 * physicalScale = TriangularCovering.H := by
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  unfold physicalScale TriangularCovering.H
  field_simp
  nlinarith

theorem referenceTetrahedron_eq_similarity :
    referenceTetrahedron = CylinderCovering.Similarity.map centeringTranslation
      (1 / 2 : ℝ) centeringIsometry '' TriangularCovering.K := by
  ext z
  constructor
  · rintro ⟨t, htlo, hthi, hx, hy, hz⟩
    refine ⟨TriangularCovering.point (2 * z 1) (2 * z 0) (t + 1 / 2), ?_, ?_⟩
    · refine ⟨2 * z 1, 2 * z 0, t + 1 / 2, by linarith, by linarith, ?_, ?_, rfl⟩
      · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith
      · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith
    · ext i
      fin_cases i
      · simp [CylinderCovering.Similarity.map, centeringTranslation, centeringIsometry,
          TriangularCovering.point, RuledApproximation.vec3]
      · simp [CylinderCovering.Similarity.map, centeringTranslation, centeringIsometry,
          TriangularCovering.point, RuledApproximation.vec3]
      · simp only [CylinderCovering.Similarity.map, centeringTranslation, centeringIsometry,
          TriangularCovering.point, RuledApproximation.vec3]
        change -physicalScale / 2 + (1 / 2 : ℝ) * (TriangularCovering.H * (t + 1 / 2)) = z 2
        rw [hz, ← twice_physicalScale]
        ring
  · rintro ⟨w, ⟨x, y, t, htlo, hthi, hx, hy, rfl⟩, rfl⟩
    refine ⟨t - 1 / 2, by linarith, by linarith, ?_, ?_, ?_⟩
    · change |0 + (1 / 2 : ℝ) * y| ≤ (1 / 2 + (t - 1 / 2)) / 2
      rw [zero_add, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith
    · change |0 + (1 / 2 : ℝ) * x| ≤ (1 / 2 - (t - 1 / 2)) / 2
      rw [zero_add, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith
    · change -physicalScale / 2 + (1 / 2 : ℝ) * (TriangularCovering.H * t) =
        physicalScale * (t - 1 / 2)
      rw [← twice_physicalScale]
      ring

theorem referenceTetrahedron_minimumShadowArea :
    CylinderCovering.minimumShadowArea referenceTetrahedron = physicalScale / 2 := by
  rw [referenceTetrahedron_eq_similarity]
  change CylinderCovering.Similarity.minimumArea
    (CylinderCovering.Similarity.map centeringTranslation (1 / 2 : ℝ)
      centeringIsometry '' TriangularCovering.K) = _
  rw [CylinderCovering.Similarity.minimumArea_map _ _ (by norm_num) centeringIsometry]
  change (1 / 2 : ℝ) ^ 2 * TriangularCovering.A_min = _
  rw [TriangularCovering.projection_minimum, ← twice_physicalScale]
  ring

end SlopeRational

end

end OAI
