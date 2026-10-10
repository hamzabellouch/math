import OAI.Geometry.ProjectionVolume.SimplexNormals
import OAI.Geometry.ProjectionVolume.FacetAreas
import OAI.Geometry.ProjectionVolume.ProjectionJacobian

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace Paper092

theorem simplexFacet_brightness (n : ℕ) (a : Option (Fin (n + 1)))
    (u : Euclidean (n + 1)) :
    brightness (simplexFacet (n + 1) a) u =
      |simplexVelocity u a| / (Nat.factorial n : ℝ) := by
  have hfac : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
  cases a with
  | some i =>
    rw [brightness_of_subset_affine_hyperplane u (EuclideanSpace.single i 1)
      (coordinate_normal_norm i) 0 _ (simplexFacet_coordinate_plane i)]
    rw [Nat.add_sub_cancel, simplexFacet_coordinate_area,
      ENNReal.toReal_ofReal (by positivity)]
    simp [EuclideanSpace.inner_single_right, simplexVelocity, div_eq_mul_inv]
  | none =>
    have hsqrt : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.mpr (by positivity)
    rw [brightness_of_subset_affine_hyperplane u (diagonalUnitNormal (n + 1))
      (diagonalUnitNormal_norm _ (Nat.succ_pos n)) (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ _
      simplexFacet_diagonal_plane]
    rw [Nat.add_sub_cancel, simplexFacet_diagonal_area,
      ENNReal.toReal_ofReal (by positivity), inner_diagonalUnitNormal]
    simp only [simplexVelocity, abs_neg, abs_div, Nat.cast_add, Nat.cast_one,
      abs_of_pos hsqrt]
    field_simp

theorem standardSimplex_brightness_succ (n : ℕ) (u : Euclidean (n + 1)) :
    brightness (standardSimplex (n + 1)) u =
      ((∑ i, |u i|) + |∑ i, u i|) / (2 * (Nat.factorial n : ℝ)) := by
  by_cases hu : u = 0
  · simp [hu, brightness]
  calc
    brightness (standardSimplex (n + 1)) u =
        ∑ a : {a : Option (Fin (n + 1)) // simplexVelocity u a < 0},
          brightness (simplexFacet (n + 1) a.val) u := by
      rw [brightness_simplex_eq_front_sum u hu, Finset.mul_sum]
      rfl
    _ = ∑ a : {a : Option (Fin (n + 1)) // simplexVelocity u a < 0},
          -simplexVelocity u a.val / (Nat.factorial n : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [simplexFacet_brightness, abs_of_neg a.property]
    _ = (∑ a : {a : Option (Fin (n + 1)) // simplexVelocity u a < 0},
          -simplexVelocity u a.val) / (Nat.factorial n : ℝ) := by rw [Finset.sum_div]
    _ = ((∑ i, |u i|) + |∑ i, u i|) / (2 * (Nat.factorial n : ℝ)) := by
      rw [simplex_front_coefficient]
      ring

theorem standardSimplex_brightness (d : ℕ) (hd : 0 < d) (u : Euclidean d) :
    brightness (standardSimplex d) u =
      ((∑ i, |u i|) + |∑ i, u i|) / (2 * (Nat.factorial (d - 1) : ℝ)) := by
  cases d with
  | zero => omega
  | succ n => simpa using standardSimplex_brightness_succ n u

end Paper092

end

end OAI
