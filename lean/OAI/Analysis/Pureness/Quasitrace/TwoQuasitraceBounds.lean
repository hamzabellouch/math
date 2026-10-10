import OAI.Analysis.Pureness.Quasitrace.ComplexQuasitraceBounds
import OAI.Analysis.Pureness.Projections.FiniteSpectralTwoQuasitrace

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped ComplexOrder CStarAlgebra IsMulCommutative
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace TwoQuasitrace
variable (T : TwoQuasitrace A)

theorem matrix_unit : T.matrix 1 = 2 * T.base 1 := by
  let p : FinMatrix A 2 := singleMatrix (0 : Fin 2) 0 1
  let q : FinMatrix A 2 := singleMatrix (1 : Fin 2) 1 1
  let v : FinMatrix A 2 := singleMatrix (0 : Fin 2) 1 1
  have hv : star v = singleMatrix (1 : Fin 2) 0 (1 : A) := by
    change CStarMatrix.ofMatrix (Matrix.single (0 : Fin 2) 1 (1 : A)).conjTranspose = _
    rw [Matrix.conjTranspose_single, star_one]
    rfl
  have hvv : v * star v = p := by rw [hv, singleMatrix_mul_same]; simp [p]
  have hvv' : star v * v = q := by rw [hv, singleMatrix_mul_same]; simp [q]
  have hpq : T.matrix q = T.matrix p := by
    simpa only [hvv, hvv'] using T.matrix.polar v
  have hp : IsSelfAdjoint p := by
    change CStarMatrix.ofMatrix (Matrix.single (0 : Fin 2) 0 (1 : A)).conjTranspose = _
    rw [Matrix.conjTranspose_single, star_one]
    rfl
  have hone : p + q = 1 := by
    apply CStarMatrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [p, q, singleMatrix, Matrix.single]
  let : IsStarNormal p := hp.isStarNormal
  let S := StarAlgebra.elemental ℂ p
  let a : S := ⟨p, StarAlgebra.elemental.self_mem ℂ p⟩
  have hq : (1 : FinMatrix A 2) - p = q := by rw [← hone]; abel
  have hadd : T.matrix 1 = T.matrix p + T.matrix q := by
    have h := (T.matrix.subalgebraLinear S).map_add a (1 - a)
    simp only [ComplexQuasitrace.subalgebraLinear_apply] at h
    change T.matrix (p + (1 - p)) = T.matrix p + T.matrix (1 - p) at h
    simpa only [hq, hone] using h
  rw [hadd, hpq]
  dsimp only [p]
  rw [← firstMatrixCorner_eq_single, ← T.extension]
  ring

theorem normalized_base_bound (hT : T.base 1 = 1) (x : A) :
    ‖T.base x‖ ≤ 8 * ‖x‖ := by
  simpa only [hT, norm_one, mul_one] using T.base.norm_apply_le x

theorem normalized_matrix_bound (hT : T.base 1 = 1) (x : FinMatrix A 2) :
    ‖T.matrix x‖ ≤ 16 * ‖x‖ := by
  have h := T.matrix.norm_apply_le x
  rw [T.matrix_unit, hT] at h
  norm_num at h ⊢
  exact h
end TwoQuasitrace
end CuntzPureness

end

end OAI
