import OAI.Analysis.Pureness.Tensor.NuclearTensorNorm
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.LinearAlgebra.TensorProduct.Pi

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped TensorProduct
variable {A B : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]

def matrixEntriesLinearEquiv (n : ℕ) (R : Type*) [AddCommGroup R] [Module ℂ R] :
    CStarMatrix (Fin n) (Fin n) R ≃ₗ[ℂ] (Fin n → Fin n → R) where
  toFun M := M
  invFun M := CStarMatrix.ofMatrix M
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def matrixTensorLinearEquiv (n : ℕ) :
    CStarMatrix (Fin n) (Fin n) A ⊗[ℂ] B ≃ₗ[ℂ]
      CStarMatrix (Fin n) (Fin n) (A ⊗[ℂ] B) :=
  (TensorProduct.congr (matrixEntriesLinearEquiv n A) (LinearEquiv.refl ℂ B)).trans
    ((TensorProduct.piLeft ℂ B (fun _ : Fin n => Fin n → A)).trans
      ((LinearEquiv.piCongrRight (fun _ : Fin n =>
        TensorProduct.piLeft ℂ B (fun _ : Fin n => A))).trans
          (matrixEntriesLinearEquiv n (A ⊗[ℂ] B)).symm))

omit [StarRing A] [StarModule ℂ A] [StarRing B] [StarModule ℂ B] in
@[simp] lemma matrixTensorLinearEquiv_tmul (n : ℕ)
    (M : CStarMatrix (Fin n) (Fin n) A) (b : B) (i j : Fin n) :
    matrixTensorLinearEquiv n (M ⊗ₜ[ℂ] b) i j = M i j ⊗ₜ[ℂ] b := by
  simp [matrixTensorLinearEquiv, TensorProduct.piLeft, matrixEntriesLinearEquiv]
  rfl

def matrixTensorStarEquiv (n : ℕ) :
    CStarMatrix (Fin n) (Fin n) A ⊗[ℂ] B ≃⋆ₐ[ℂ]
      CStarMatrix (Fin n) (Fin n) (A ⊗[ℂ] B) where
  __ := matrixTensorLinearEquiv n
  map_mul' x y := by
    change matrixTensorLinearEquiv n (x*y) = matrixTensorLinearEquiv n x * matrixTensorLinearEquiv n y
    induction x using TensorProduct.inductionOn with
    | add x z hx hz => simp only [add_mul, map_add, hx, hz]
    | tmul M b =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => simp only [mul_add, map_add, hy, hz]
      | tmul N c =>
        ext i j
        simp only [Algebra.TensorProduct.tmul_mul_tmul, matrixTensorLinearEquiv_tmul,
          CStarMatrix.mul_apply, TensorProduct.sum_tmul, matrixTensorLinearEquiv_tmul,
          Algebra.TensorProduct.tmul_mul_tmul]
  map_star' x := by
    change matrixTensorLinearEquiv n (star x) = star (matrixTensorLinearEquiv n x)
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [star_add, map_add, hx, hy]
    | tmul M b =>
      ext i j
      simp only [TensorProduct.star_tmul, matrixTensorLinearEquiv_tmul, CStarMatrix.star_apply]

@[simp] lemma matrixTensorStarEquiv_tmul (n : ℕ)
    (M : CStarMatrix (Fin n) (Fin n) A) (b : B) (i j : Fin n) :
    matrixTensorStarEquiv n (M ⊗ₜ[ℂ] b) i j = M i j ⊗ₜ[ℂ] b := matrixTensorLinearEquiv_tmul n M b i j
end CuntzPureness

end

end OAI
