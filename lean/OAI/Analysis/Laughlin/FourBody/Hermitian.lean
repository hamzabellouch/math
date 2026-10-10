import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import OAI.Analysis.Laughlin.FourBody.Support

namespace OAI

namespace Laughlin.Spin
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem list_double_sum_swap {I A : Type*} [AddCommMonoid A]
    (l k : List I) (f : I → I → A) :
    (l.map (fun i => (k.map (f i)).sum)).sum =
      (k.map (fun j => (l.map (fun i => f i j)).sum)).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons,List.sum_cons,ih,List.sum_map_add]

theorem fourBodyTermMatrix_transpose (Q t : ℕ) (e f : ℕ × ℕ × ℤ) :
    (fourBodyTermMatrix Q t e f)ᵀ = fourBodyTermMatrix Q t f e := by
  ext i j
  simp only [fourBodyTermMatrix,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul,realOuter]
  ring

theorem physicalFourBodyMatrix_transpose (Q : ℕ) :
    (physicalFourBodyMatrix Q)ᵀ = physicalFourBodyMatrix Q := by
  unfold physicalFourBodyMatrix
  simp only [Matrix.transpose_list_sum,List.map_map,Function.comp_def,fourBodyTermMatrix_transpose]
  congr 1
  apply List.map_congr_left
  intro row hrow
  exact list_double_sum_swap row.2.2 row.2.2 (fun e f => fourBodyTermMatrix Q row.1 f e)

theorem physicalFourBodyMatrix_hermitian (Q : ℕ) :
    ((physicalFourBodyMatrix Q).map Complex.ofReal)ᴴ = (physicalFourBodyMatrix Q).map Complex.ofReal := by
  rw [real_matrix_adjoint,physicalFourBodyMatrix_transpose]

theorem physicalFourBodyHaar_hermitian (Q : ℕ) :
    (matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)))ᴴ =
    matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)) := by
  have he (g : SourceSU2) :
      (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal) g)ᴴ =
      conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal) g := by
    simp only [conjugateOrbit,Matrix.conjTranspose_mul,fourBodySpinRepresentation_inv,
      Matrix.conjTranspose_conjTranspose,physicalFourBodyMatrix_hermitian,Matrix.mul_assoc]
  ext i j
  change star (∫ g, conjugateOrbit (fourBodySpinRepresentation Q)
    ((physicalFourBodyMatrix Q).map Complex.ofReal) g j i ∂sourceHaar) = _
  calc
    _ = ∫ g, star (conjugateOrbit (fourBodySpinRepresentation Q)
      ((physicalFourBodyMatrix Q).map Complex.ofReal) g j i) ∂sourceHaar := integral_conj.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with g
      exact congrFun (congrFun (he g) i) j

end Laughlin.Spin

end OAI
