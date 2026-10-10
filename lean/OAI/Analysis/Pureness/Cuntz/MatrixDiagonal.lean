import Mathlib.Algebra.Order.Star.Pi
import OAI.Analysis.Pureness.Cuntz.MatrixTraces
import OAI.Analysis.Pureness.Traces.RootFunctoriality
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi

namespace OAI
namespace CuntzPureness
open scoped ComplexOrder ENNReal NNReal
open Filter Topology
variable {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def diagonalMatrixHom : (ι → A) →⋆ₐ[ℂ] CStarMatrix ι ι A :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    { Matrix.diagonalAlgHom ℂ with
      map_star' := by
        intro a
        exact (Matrix.diagonal_conjTranspose a).symm }

@[simp] lemma diagonalMatrixHom_apply (a : ι → A) (i j : ι) :
    diagonalMatrixHom a i j = if i = j then a i else 0 := rfl

variable [PartialOrder A] [StarOrderedRing A]

lemma diagonalMatrix_nonneg (a : ι → A) (ha : ∀ i, 0 ≤ a i) :
    0 ≤ diagonalMatrixHom a := by
  exact starAlgHom_positive diagonalMatrixHom a ha

lemma positivePower_diagonal (a : ι → A) (ha : ∀ i, 0 ≤ a i)
    (r : ℝ≥0) (hr : 0 < r) :
    positivePower (diagonalMatrixHom a) r =
      diagonalMatrixHom (fun i => positivePower (a i) r) := by
  rw [positivePower_map diagonalMatrixHom a ha r hr]
  congr 1
  funext i
  exact (positivePower_map (Pi.evalStarAlgHom ℂ (fun _ : ι => A) i) a ha r hr).symm

lemma matrixTrace_positivePower_diagonal (τ : TracialState A) (a : ι → A)
    (ha : ∀ i, 0 ≤ a i) (r : ℝ≥0) (hr : 0 < r) :
    matrixTrace τ (positivePower (diagonalMatrixHom a) r) =
      ∑ i, τ.functional (positivePower (a i) r) := by
  rw [positivePower_diagonal a ha r hr]
  simp only [matrixTrace_apply, diagonalMatrixHom_apply, ite_true]
end CuntzPureness

end OAI
