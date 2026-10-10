import OAI.Geometry.EinsteinFour.GradientCasimir

namespace OAI

/-! The compressed derivative generator in the actual quaternion model. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

/-- The Clifford anticommutator, with the normalization of the fixed frame. -/
theorem quaternion_anticommutator (r s : Fin 3) (q : Vec) :
    quaternion r (quaternion s q) + quaternion s (quaternion r q) =
      if r = s then (-2 : ℝ) • q else 0 := by
  fin_cases r <;> fin_cases s <;> ext u <;> fin_cases u <;>
    simp [quaternion]
  all_goals ring

/-- The matrix-slot curvature operator for a diagonal trace-free curvature block. -/
def diagonalCurvatureAction (t : Fin 3 → ℝ) (M : Mat) : Mat := fun a b =>
  (t a + t b) / 2 * M a b -
    if a = b then (∑ c, t c * M c c) / 3 else 0

/-- The normalization of the spin-two curvature operator is a direct
five-coordinate identity. -/
theorem weighted_matrixAction_square (t : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (M : Mat) (hs : symmetric M) (hm : traceFree M) :
    (∑ s, t s • matrixAction s (matrixAction s M)) =
      (24 : ℝ) • diagonalCurvatureAction t M := by
  have ht2 : t 2 = -t 0 - t 1 := by
    have h := ht
    simp only [Fin.sum_univ_three] at h
    linarith
  ext a b
  change (∑ s, t s * matrixAction s (matrixAction s M) a b) =
    24 * diagonalCurvatureAction t M a b
  rw [← coordinates_eq M hs hm]
  simp only [Fin.sum_univ_three, matrixAction_coordinates_zero,
    matrixAction_coordinates_one, matrixAction_coordinates_two]
  fin_cases a <;> fin_cases b <;>
    simp [diagonalCurvatureAction, ofCoordinates, Fin.sum_univ_succ, ht2]
  all_goals ring

/-- Apply a quaternion only in the derivative slot of a matrix-valued tensor. -/
def derivativeQuaternion (r : Fin 3) (Z : Tensor) : Tensor where
  diagonal a := quaternion r (Z.diagonal a)
  off a := quaternion r (Z.off a)

@[simp] theorem derivativeQuaternion_matrix (r : Fin 3) (Z : Tensor)
    (a b : Fin 3) :
    (derivativeQuaternion r Z).matrix a b = quaternion r (Z.matrix a b) := by
  fin_cases a <;> fin_cases b <;> rfl

/-- Matrix rotations commute with the action on the derivative slot. -/
theorem matrixRotation_derivativeQuaternion (r s : Fin 3) (Z : Tensor)
    (a b : Fin 3) :
    matrixRotation s (derivativeQuaternion r Z) a b =
      quaternion r (matrixRotation s Z a b) := by
  simp only [matrixRotation, derivativeQuaternion_matrix, Fin.sum_univ_three]
  simp only [sub_eq_add_neg, quaternion_add, quaternion_neg, quaternion_smul]

/-- The exact anticommutator between the Bianchi coupling and a derivative
quaternion. No irreducible-representation assertion is assumed. -/
theorem gradientCoupling_anticommutator (r : Fin 3) (Z : Tensor)
    (a b : Fin 3) :
    gradientCoupling (derivativeQuaternion r Z) a b +
      quaternion r (gradientCoupling Z a b) = (-2 : ℝ) • matrixRotation r Z a b := by
  simp only [gradientCoupling, matrixRotation_derivativeQuaternion,
    Fin.sum_univ_three, quaternion_add]
  have h0 := quaternion_anticommutator 0 r (matrixRotation 0 Z a b)
  have h1 := quaternion_anticommutator 1 r (matrixRotation 1 Z a b)
  have h2 := quaternion_anticommutator 2 r (matrixRotation 2 Z a b)
  calc
    _ = (quaternion 0 (quaternion r (matrixRotation 0 Z a b)) +
          quaternion r (quaternion 0 (matrixRotation 0 Z a b))) +
        (quaternion 1 (quaternion r (matrixRotation 1 Z a b)) +
          quaternion r (quaternion 1 (matrixRotation 1 Z a b))) +
        (quaternion 2 (quaternion r (matrixRotation 2 Z a b)) +
          quaternion r (quaternion 2 (matrixRotation 2 Z a b))) := by module
    _ = _ := by
      rw [h0, h1, h2]
      fin_cases r <;> norm_num


/-- The polynomial expression for the orthogonal Bianchi projector. -/
def gradientProjection (Z : Tensor) (a b : Fin 3) : Vec :=
  (1 / 10 : ℝ) • ((6 : ℝ) • Z.matrix a b - gradientCoupling Z a b)

/-- The projector fixes every actual Bianchi tensor. -/
theorem gradientProjection_eq (Z : Tensor) (hb : Z.bianchi) (a b : Fin 3) :
    gradientProjection Z a b = Z.matrix a b := by
  rw [gradientProjection, gradientCoupling_eq Z hb]
  module

/-- Compressing the derivative quaternion to the Bianchi subspace gives one
fifth of the total inner generator, with the coefficient derived explicitly. -/
theorem gradientProjection_derivativeQuaternion (r : Fin 3) (Z : Tensor)
    (hb : Z.bianchi) (a b : Fin 3) :
    gradientProjection (derivativeQuaternion r Z) a b =
      (1 / 5 : ℝ) • gradientGenerator r Z a b := by
  have h := gradientCoupling_anticommutator r Z a b
  rw [gradientCoupling_eq Z hb, quaternion_smul] at h
  rw [gradientProjection, derivativeQuaternion_matrix, gradientGenerator,
    eq_sub_of_add_eq h]
  module

end
end PositiveEinsteinFour.Bianchi

end OAI
