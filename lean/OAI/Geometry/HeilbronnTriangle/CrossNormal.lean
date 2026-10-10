import OAI.Geometry.HeilbronnTriangle.PrimitiveNormal

namespace OAI


namespace Problem355.CrossNormal

open Matrix
open scoped Matrix
open PrimitiveNormal

lemma toEuclidean_zsmul (g : ℤ) (w : Vector) :
    toEuclidean (g • w) = (g : ℝ) • toEuclidean w := by
  ext i
  simp [PrimitiveNormal.toEuclidean, Pi.smul_apply, smul_eq_mul]

theorem norm_cross_le (u v : Vector) :
    ‖toEuclidean (u ⨯₃ v)‖ ≤ ‖toEuclidean u‖ * ‖toEuclidean v‖ := by
  let d : ℝ := ∑ i : Fin 3, (u i : ℝ) * (v i : ℝ)
  have hlagrange : ‖toEuclidean (u ⨯₃ v)‖ ^ 2 + d ^ 2 =
      ‖toEuclidean u‖ ^ 2 * ‖toEuclidean v‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq]
    simp [PrimitiveNormal.toEuclidean, d, Fin.sum_univ_three, cross_apply]
    ring
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  calc
    ‖toEuclidean (u ⨯₃ v)‖ ^ 2 ≤
        ‖toEuclidean u‖ ^ 2 * ‖toEuclidean v‖ ^ 2 := by nlinarith [sq_nonneg d]
    _ = (‖toEuclidean u‖ * ‖toEuclidean v‖) ^ 2 := by ring

theorem norm_le_of_positive_factor {v w : Vector} {g : ℤ}
    (hg : 0 < g) (hscale : v = g • w) : ‖toEuclidean w‖ ≤ ‖toEuclidean v‖ := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  rw [hscale, toEuclidean_zsmul, norm_smul, Real.norm_eq_abs, abs_of_pos hgR]
  nlinarith [norm_nonneg (toEuclidean w)]

theorem determinant_eq_factor_dot {u v w : Vector} {g : ℤ}
    (hscale : u ⨯₃ v = g • w) (x : Vector) :
    Matrix.det ![x, u, v] = g * (x ⬝ᵥ w) := by
  rw [← triple_product_eq_det, hscale, dotProduct_smul, smul_eq_mul]

theorem determinant_eq_iff_difference_dot_zero {u v w : Vector} {g : ℤ}
    (hg : g ≠ 0) (hscale : u ⨯₃ v = g • w) (x z : Vector) :
    Matrix.det ![x, u, v] = Matrix.det ![z, u, v] ↔ (x - z) ⬝ᵥ w = 0 := by
  rw [determinant_eq_factor_dot hscale, determinant_eq_factor_dot hscale,
    sub_dotProduct, sub_eq_zero]
  constructor
  · exact mul_left_cancel₀ hg
  · intro h
    rw [h]

theorem exists_bounded_primitive_cross_factor (u v : Vector) (huv : u ⨯₃ v ≠ 0) :
    ∃ g : ℤ, 0 < g ∧ ∃ w : Vector, IsPrimitive w ∧ u ⨯₃ v = g • w ∧
      u ⬝ᵥ w = 0 ∧ v ⬝ᵥ w = 0 ∧
      ‖toEuclidean w‖ ≤ ‖toEuclidean u‖ * ‖toEuclidean v‖ ∧
      (∀ x z : Vector, Matrix.det ![x, u, v] = Matrix.det ![z, u, v] ↔
        (x - z) ⬝ᵥ w = 0) := by
  obtain ⟨g, hg, w, hw, hscale⟩ := exists_primitive_factor (u ⨯₃ v) huv
  have horth (x : Vector) (hx : x ⬝ᵥ u ⨯₃ v = 0) : x ⬝ᵥ w = 0 := by
    rw [hscale, dotProduct_smul, smul_eq_mul] at hx
    exact (mul_eq_zero.mp hx).resolve_left (ne_of_gt hg)
  refine ⟨g, hg, w, hw, hscale, horth u (dot_self_cross u v),
    horth v (dot_cross_self u v), ?_, ?_⟩
  · exact (norm_le_of_positive_factor hg hscale).trans (norm_cross_le u v)
  · exact determinant_eq_iff_difference_dot_zero (ne_of_gt hg) hscale

end Problem355.CrossNormal

end OAI
