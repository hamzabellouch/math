import OAI.Analysis.BoundedHochschild.PositiveBlockRegularization
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

namespace OAI

/-! Entrywise scalar matrices and their action on matrix amplifications. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def scalarMatrixHom (A : Type*) [CStarAlgebra A] (n : ℕ) :
    CStarMatrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A where
  toFun Q := Q.map (algebraMap ℂ A)
  map_zero' := by ext i j; exact map_zero (algebraMap ℂ A)
  map_add' Q R := by ext i j; exact map_add (algebraMap ℂ A) (Q i j) (R i j)
  map_one' := by
    ext i j
    change algebraMap ℂ A (if i = j then 1 else 0) = if i = j then 1 else 0
    split_ifs <;> simp
  map_mul' Q R := by
    ext i j
    change algebraMap ℂ A (∑ k, Q i k * R k j) =
      ∑ k, algebraMap ℂ A (Q i k) * algebraMap ℂ A (R k j)
    simp
  commutes' z := by
    ext i j
    change algebraMap ℂ A (if i = j then z else 0) =
      if i = j then algebraMap ℂ A z else 0
    split_ifs <;> simp
  map_star' Q := by
    ext i j
    exact map_star (StarAlgHom.ofId ℂ A) (Q j i)

@[simp] lemma scalarMatrixHom_apply (n : ℕ)
    (Q : CStarMatrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    scalarMatrixHom A n Q i j = algebraMap ℂ A (Q i j) := rfl

lemma scalarMatrixHom_injective [Nontrivial A] (n : ℕ) :
    Function.Injective (scalarMatrixHom A n) :=
  CStarMatrix.map_injective (algebraMap ℂ A).injective

def entrywiseMatrixLinear (T : A →ₗ[ℂ] B) (n : ℕ) :
    CStarMatrix (Fin n) (Fin n) A →ₗ[ℂ] CStarMatrix (Fin n) (Fin n) B :=
  CStarMatrix.mapₗ T

lemma linearMap_scalar_multiply (T : A →ₗ[ℂ] B) (z w : ℂ) (a : A) :
    T (algebraMap ℂ A z * a * algebraMap ℂ A w) =
      algebraMap ℂ B z * T a * algebraMap ℂ B w := by
  simp [Algebra.algebraMap_eq_smul_one]

lemma entrywiseMatrixLinear_scalar_actions (T : A →ₗ[ℂ] B) (n : ℕ)
    (Q R : CStarMatrix (Fin n) (Fin n) ℂ) (X : CStarMatrix (Fin n) (Fin n) A) :
    entrywiseMatrixLinear T n (scalarMatrixHom A n Q * X * scalarMatrixHom A n R) =
      scalarMatrixHom B n Q * entrywiseMatrixLinear T n X * scalarMatrixHom B n R := by
  apply CStarMatrix.ext
  intro i j
  change T (∑ k, (∑ l, algebraMap ℂ A (Q i l) * X l k) * algebraMap ℂ A (R k j)) =
    ∑ k, (∑ l, algebraMap ℂ B (Q i l) * T (X l k)) * algebraMap ℂ B (R k j)
  simp only [Finset.sum_mul, map_sum, linearMap_scalar_multiply]

end BoundedHochschild.KadisonRingrose

end

end OAI
