import OAI.Analysis.KadisonKastler.MatrixCommutant
import OAI.Analysis.KadisonKastler.CompletelyPositive
import Mathlib.Algebra.Star.UnitaryStarAlgAut

namespace OAI

/-! # The complete displacement of an inner conjugation -/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Inner conjugation, with its linear-map structure. -/
def unitaryConjugationLinear (u : unitary B) : B →ₗ[ℂ] B :=
  (Unitary.conjStarAlgAut ℂ B u).toAlgEquiv.toLinearMap

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem unitaryConjugationLinear_apply (u : unitary B) (x : B) :
    unitaryConjugationLinear u x = (u : B) * x * star (u : B) := rfl

/-- The same displacement bound holds at every rectangular matrix level. -/
theorem complete_unitaryConjugation_sub_id (u : unitary B) :
    CompletelyBoundedBy (unitaryConjugationLinear u - LinearMap.id)
      (2 * ‖(u : B) - 1‖) := by
  intro p q X
  nontriviality B
  let P : CStarMatrix (Fin p) (Fin p) B := matrixScalarHom (u : B)
  let Q : CStarMatrix (Fin q) (Fin q) B := matrixScalarHom (star (u : B))
  have hQ : ‖Q‖ ≤ 1 := by
    exact (NonUnitalStarAlgHom.norm_apply_le
      (matrixScalarHom : B →⋆ₐ[ℂ] CStarMatrix (Fin q) (Fin q) B) _).trans_eq
        (by simp)
  have hPsub : ‖P - 1‖ ≤ ‖(u : B) - 1‖ := by
    simpa only [map_sub, map_one] using NonUnitalStarAlgHom.norm_apply_le
      (matrixScalarHom : B →⋆ₐ[ℂ] CStarMatrix (Fin p) (Fin p) B) ((u : B) - 1)
  have hQsub : ‖Q - 1‖ ≤ ‖(u : B) - 1‖ := by
    have h := NonUnitalStarAlgHom.norm_apply_le
      (matrixScalarHom : B →⋆ₐ[ℂ] CStarMatrix (Fin q) (Fin q) B) (star (u : B) - 1)
    have hs : ‖star (u : B) - 1‖ = ‖(u : B) - 1‖ := by
      simpa only [star_sub, star_one] using norm_star ((u : B) - 1)
    simpa only [map_sub, map_one, hs] using h
  have hmatrix : CStarMatrix.mapₗ (unitaryConjugationLinear u) X = P * X * Q := by
    ext i j
    simp [P, Q, CStarMatrix.mul_apply, matrixScalarHom_apply]
  have hid : P * X * Q - X = (P - 1) * X * Q + X * (Q - 1) := by
    have hm (A : Matrix (Fin p) (Fin p) B) (Y : Matrix (Fin p) (Fin q) B)
        (D : Matrix (Fin q) (Fin q) B) :
        A * Y * D - Y = (A - 1) * Y * D + Y * (D - 1) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
      abel
    exact hm P X Q
  rw [matrix_map_sub, hmatrix]
  change ‖P * X * Q - X‖ ≤ _
  rw [hid]
  calc
    _ ≤ ‖(P - 1) * X * Q‖ + ‖X * (Q - 1)‖ := norm_add_le _ _
    _ ≤ (‖P - 1‖ * ‖X‖) * ‖Q‖ + ‖X‖ * ‖Q - 1‖ :=
      add_le_add ((rectangular_norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (rectangular_norm_mul_le _ _) (norm_nonneg Q)))
        (rectangular_norm_mul_le _ _)
    _ ≤ (‖(u : B) - 1‖ * ‖X‖) * 1 + ‖X‖ * ‖(u : B) - 1‖ := by
      gcongr
    _ = 2 * ‖(u : B) - 1‖ * ‖X‖ := by ring

end

end KadisonKastler

end OAI
