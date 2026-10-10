import OAI.Combinatorics.EuclideanRamsey.NineGeometry
import OAI.Combinatorics.EuclideanRamsey.NineField
import OAI.Combinatorics.EuclideanRamsey.NineRationalDeterminant
import OAI.Combinatorics.EuclideanRamsey.NineLinearObstruction
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

/-! Nine algebraically independent circle parameters give a non-Ramsey configuration. -/

noncomputable section
namespace EuclideanRamsey.NineMain

local instance parameterFieldAlgebra : Algebra ℚ NineField.ParameterField :=
  NineField.parameterFieldAlgebra

local instance targetFieldAlgebra : Algebra ℚ NineField.TargetField :=
  NineField.targetFieldAlgebra

open NineGeometry
open scoped TensorProduct

def gridToFin9 : NineGrid.Index ≃ Fin 9 := finProdFinEquiv

def gridToColumn : NineGrid.Index ≃ NineLinearObstruction.Column 2 :=
  Equiv.prodCongr (finSuccEquiv 2) (finSuccEquiv 2)

def rowEquiv : NineLinearObstruction.Column 2 ≃ Fin 9 :=
  gridToColumn.symm.trans gridToFin9

/-- Renaming the polynomial variables into the independent-variable field. -/
def polynomialEmbedding : NineGrid.Poly →+* NineField.TargetField :=
  (algebraMap NineField.TargetPoly NineField.TargetField).comp
    (MvPolynomial.renameEquiv ℚ (Equiv.sumCongr gridToFin9 gridToFin9)).toRingHom

theorem polynomialEmbedding_injective : Function.Injective polynomialEmbedding :=
  (IsFractionRing.injective NineField.TargetPoly NineField.TargetField).comp
    (MvPolynomial.renameEquiv ℚ (Equiv.sumCongr gridToFin9 gridToFin9)).injective

@[simp] theorem polynomialEmbedding_T (i : NineGrid.Index) :
    polynomialEmbedding (NineGrid.T i) = NineField.T (gridToFin9 i) := by
  simp [polynomialEmbedding, NineGrid.T, NineField.T]

@[simp] theorem polynomialEmbedding_U (i : NineGrid.Index) :
    polynomialEmbedding (NineGrid.U i) = NineField.U (gridToFin9 i) := by
  simp [polynomialEmbedding, NineGrid.U, NineField.U]

theorem paramVector_eq_r (z : NineField.TargetField) (a : Option (Fin 2)) :
    NineField.paramVector z a = NineRational.r z ((finSuccEquiv 2).symm a) := by
  cases a with
  | none => simp [NineField.paramVector, NineField.a0, NineRational.r]
  | some a => fin_cases a <;>
      simp [NineField.paramVector, NineField.a1, NineField.a2, NineRational.r]

/-- The tensor evaluation matrix is the rational-coordinate matrix after reindexing. -/
theorem evaluationMatrix_eq (t : Fin 9 → ℝ) (ht : AlgebraicIndependent ℚ t) :
    NineLinearObstruction.evaluationMatrix (circleConfig t)
      (NineField.coordinateTensorEmbedding t ht) rowEquiv =
    Matrix.reindex gridToColumn gridToColumn
      (NineRational.genericMatrix polynomialEmbedding) := by
  ext i q
  simp only [NineLinearObstruction.evaluationMatrix,
    NineField.coordinateTensorEmbedding_tmul, map_one, mul_one, one_mul,
    NineField.leftCoeff_augmented, NineField.rightCoeff_augmented]
  simp only [paramVector_eq_r, Matrix.reindex_apply, Matrix.submatrix_apply,
    NineRational.genericMatrix,
    polynomialEmbedding_T, polynomialEmbedding_U]
  rfl

theorem evaluationMatrix_det_ne_zero (t : Fin 9 → ℝ)
    (ht : AlgebraicIndependent ℚ t) :
    (NineLinearObstruction.evaluationMatrix (circleConfig t)
      (NineField.coordinateTensorEmbedding t ht) rowEquiv).det ≠ 0 := by
  rw [evaluationMatrix_eq, Matrix.det_reindex_self]
  exact NineRational.det_genericMatrix_ne_zero polynomialEmbedding
    polynomialEmbedding_injective

/-- Nine algebraically independent real parameters give a non-Ramsey configuration. -/
theorem nine_circle_not_ramsey (t : Fin 9 → ℝ)
    (ht : AlgebraicIndependent ℚ t) : ¬ Ramsey (circleConfig t) := by
  exact NineLinearObstruction.not_ramsey_of_det_ne_zero (circleConfig t)
    (by decide) (by decide) (circleConfig_affineSpan t ht)
    (NineField.coordinateTensorEmbedding t ht)
    (NineField.coordinateTensorEmbedding_injective t ht) rowEquiv
    (evaluationMatrix_det_ne_zero t ht)

/-- Nine distinct points on the unit circle form a non-Ramsey configuration. -/
theorem nine_circle_configuration (t : Fin 9 → ℝ)
    (ht : AlgebraicIndependent ℚ t) :
    Function.Injective (circleConfig t) ∧
      (∀ i, dist (circleConfig t i) 0 = 1) ∧ ¬ Ramsey (circleConfig t) :=
  ⟨circleConfig_injective t ht, circleConfig_on_circle t, nine_circle_not_ramsey t ht⟩

end EuclideanRamsey.NineMain

end

end OAI
