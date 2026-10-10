import OAI.Algebra.AuslanderReiten.Homology.RestrictionProjective
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory
open scoped TensorProduct

universe u

variable (k R S : Type u) [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def tensorLeftInclusion : R →+* R ⊗[k] S :=
  (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] S).toRingHom

def tensorRightInclusion : S →+* R ⊗[k] S :=
  (Algebra.TensorProduct.includeRight : S →ₐ[k] R ⊗[k] S).toRingHom

def tensorLeftRegularEquiv :
    ((ModuleCat.restrictScalars (tensorLeftInclusion k R S)).obj (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S))) ≃ₗ[R]
      R ⊗[k] S where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r z := by
    change ((r ⊗ₜ[k] (1 : S)) * (show R ⊗[k] S from z)) = r • (show R ⊗[k] S from z)
    let x : R ⊗[k] S := z
    change (r ⊗ₜ[k] (1 : S)) * x = r • x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp [mul_add, smul_add, hx, hy]
    | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul', smul_eq_mul]

def tensorRightRegularEquiv :
    ((ModuleCat.restrictScalars (tensorRightInclusion k R S)).obj (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S))) ≃ₗ[S]
      S ⊗[k] R where
  __ := (TensorProduct.comm k R S).toAddEquiv
  map_smul' s z := by
    let x : R ⊗[k] S := z
    change TensorProduct.comm k R S (((1 : R) ⊗ₜ[k] s) * x) =
      s • TensorProduct.comm k R S x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp [mul_add, smul_add, hx, hy]
    | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul', smul_eq_mul]

theorem tensorLeftRegular_projective :
    Module.Projective R ((ModuleCat.restrictScalars (tensorLeftInclusion k R S)).obj
      (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S))) :=
  Module.Projective.of_equiv (tensorLeftRegularEquiv k R S).symm

theorem tensorRightRegular_projective :
    Module.Projective S ((ModuleCat.restrictScalars (tensorRightInclusion k R S)).obj
      (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S))) :=
  Module.Projective.of_equiv (tensorRightRegularEquiv k R S).symm

theorem tensorLeftRegular_finite [Module.Finite k S] :
    Module.Finite R ((ModuleCat.restrictScalars (tensorLeftInclusion k R S)).obj
      (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S))) := by
  let : Module.Finite R (R ⊗[k] S) := Module.Finite.of_basis ((Module.finBasis k S).baseChange R)
  exact Module.Finite.equiv (tensorLeftRegularEquiv k R S).symm

theorem tensorRightRegular_finite [Module.Finite k R] :
    Module.Finite S ((ModuleCat.restrictScalars (tensorRightInclusion k R S)).obj
      (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S))) := by
  let : Module.Finite S (S ⊗[k] R) := Module.Finite.of_basis ((Module.finBasis k R).baseChange S)
  exact Module.Finite.equiv (tensorRightRegularEquiv k R S).symm

end ArExplicit

end

end OAI
