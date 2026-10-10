import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorExact
import Mathlib.Algebra.Homology.Single

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

instance diagonalZeroUnique : Unique (Diagonal 0) where
  default := ⟨(0,0),rfl⟩
  uniq p := by
    apply Subtype.ext
    apply Prod.ext <;> have h := p.property <;> dsimp at * <;> omega

variable (M : ModuleCat.{u} A) (N : ModuleCat.{u} B)

abbrev singleTotal := complex k A B ((ChainComplex.single₀ (ModuleCat A)).obj M)
  ((ChainComplex.single₀ (ModuleCat B)).obj N)

def singleTotalZeroEquiv : (singleTotal k A B M N).X 0 ≃ₗ[A ⊗[k] B]
    moduleObject k A B M N :=
  (termPiEquiv k A B _ _ 0).trans
    { Equiv.piUnique (fun p : Diagonal 0 =>
        summands k A B ((ChainComplex.single₀ (ModuleCat A)).obj M)
          ((ChainComplex.single₀ (ModuleCat B)).obj N) 0 p) with
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

theorem singleTotal_summand_isZero (n : ℕ) (hn : n ≠ 0) (p : Diagonal n) :
    IsZero (summands k A B ((ChainComplex.single₀ (ModuleCat A)).obj M)
      ((ChainComplex.single₀ (ModuleCat B)).obj N) n p) := by
  by_cases hi : p.val.1 = 0
  · have hj : p.val.2 ≠ 0 := by have h := p.property; omega
    exact (rightFunctor k A B (((ChainComplex.single₀ (ModuleCat A)).obj M).X p.val.1)).map_isZero
      (isZero_single_obj_X _ _ _ _ hj)
  · exact ((bifunctor k A B).flip.obj (((ChainComplex.single₀ (ModuleCat B)).obj N).X p.val.2)).map_isZero
      (isZero_single_obj_X _ _ _ _ hi)

theorem singleTotal_isZero (n : ℕ) (hn : n ≠ 0) : IsZero ((singleTotal k A B M N).X n) := by
  have (p : Diagonal n) : Subsingleton
      (summands k A B ((ChainComplex.single₀ (ModuleCat A)).obj M)
        ((ChainComplex.single₀ (ModuleCat B)).obj N) n p) :=
    ModuleCat.subsingleton_of_isZero (singleTotal_summand_isZero k A B M N n hn p)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact (termPiEquiv k A B _ _ n).injective.subsingleton

def singleTotalTermIso (n : ℕ) : (singleTotal k A B M N).X n ≅
    ((ChainComplex.single₀ (ModuleCat (A ⊗[k] B))).obj (moduleObject k A B M N)).X n := by
  by_cases hn : n=0
  · subst n
    exact (singleTotalZeroEquiv k A B M N).toModuleIso
  · exact (singleTotal_isZero k A B M N n hn).iso (isZero_single_obj_X _ _ _ _ hn)

def singleTotalIso : singleTotal k A B M N ≅
    (ChainComplex.single₀ (ModuleCat (A ⊗[k] B))).obj (moduleObject k A B M N) :=
  HomologicalComplex.Hom.isoOfComponents (singleTotalTermIso k A B M N) (by
    intro i j hij
    have hi : i ≠ 0 := by change j+1=i at hij; omega
    exact (singleTotal_isZero k A B M N i hi).eq_of_src _ _)

end ArExplicit.ExternalTensor

end

end OAI
