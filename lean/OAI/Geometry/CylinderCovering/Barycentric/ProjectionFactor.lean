import OAI.Geometry.CylinderCovering.Barycentric.Cost
import OAI.Geometry.CylinderCovering.Barycentric.Correspondence

namespace OAI

open scoped InnerProductSpace

noncomputable section
namespace RadialCoordinates

theorem intercept_gram :
    inner ℝ interceptTangentA interceptTangentA = (3 / 2 : ℝ) ∧
    inner ℝ interceptTangentB interceptTangentB = (3 / 2 : ℝ) ∧
    inner ℝ interceptTangentA interceptTangentB = (1 / 2 : ℝ) := by
  norm_num [interceptTangentA, interceptTangentB, EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.real_norm_sq_eq, dotProduct, Fin.sum_univ_succ]

theorem intercept_gram_determinant :
    inner ℝ interceptTangentA interceptTangentA *
      inner ℝ interceptTangentB interceptTangentB -
      (inner ℝ interceptTangentA interceptTangentB) ^ 2 = (2 : ℝ) := by
  rw [intercept_gram.1, intercept_gram.2.1, intercept_gram.2.2]
  norm_num

theorem firstDirection_sum (k t : ℝ) : ∑ i, firstDirection k t i = 0 := by
  simp [firstDirection, angular, Fin.sum_univ_succ]
  ring

theorem firstSweep_line_direction (k S t p p' : ℝ) :
    firstSweepPoint k t S p - firstSweepPoint k t S p' =
      (p - p') • firstDirection k t := by
  ext i
  fin_cases i <;> simp [firstSweepPoint, barycentricPoint, firstDirection, angular] <;> ring

theorem firstDirection_norm_squared (k t : ℝ) :
    ‖firstDirection k t‖ ^ 2 = (1 + k ^ 2 * speedSquared t) / 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [firstDirection, speedSquared, angular, Fin.sum_univ_succ]
  ring

theorem firstDirection_ne_zero (k t : ℝ) : firstDirection k t ≠ 0 := by
  intro h
  have hn := firstDirection_norm_squared k t
  rw [h, norm_zero] at hn
  have hE : 0 ≤ speedSquared t := by unfold speedSquared; positivity
  nlinarith [mul_nonneg (sq_nonneg k) hE]

theorem interceptNormal_norm : ‖interceptNormal‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  norm_num [interceptNormal, Fin.sum_univ_succ, div_pow, hsqrt]

theorem interceptNormal_tangent_orthogonal :
    inner ℝ interceptNormal interceptTangentA = 0 ∧
    inner ℝ interceptNormal interceptTangentB = 0 := by
  simp [interceptNormal, interceptTangentA, interceptTangentB,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
  ring

theorem firstDirection_normal_inner (k t : ℝ) :
    inner ℝ interceptNormal (firstDirection k t) = 1 / Real.sqrt 2 := by
  simp [interceptNormal, firstDirection,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
  ring

theorem firstDirection_projection_cosine (k t : ℝ) :
    inner ℝ interceptNormal (firstDirection k t) / ‖firstDirection k t‖ =
      1 / Real.sqrt (1 + k ^ 2 * speedSquared t) := by
  rw [firstDirection_normal_inner]
  have hE : 0 ≤ speedSquared t := by unfold speedSquared; positivity
  have hx : 0 < 1 + k ^ 2 * speedSquared t := by positivity
  have hn : 0 < ‖firstDirection k t‖ := norm_pos_iff.mpr (firstDirection_ne_zero k t)
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hxroot : 0 < Real.sqrt (1 + k ^ 2 * speedSquared t) := Real.sqrt_pos.2 hx
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  simp only [div_pow, one_pow]
  rw [firstDirection_norm_squared, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt hx.le]
  field_simp

end RadialCoordinates

end

end OAI
