import OAI.Algebra.Finitistic.Ordinary.OrdinaryBlockComplexes
import OAI.Algebra.Finitistic.Ordinary.OrdinaryFirstBlockTensor
import OAI.Algebra.Finitistic.Ordinary.OrdinarySecondBlockTensor
import OAI.Algebra.Finitistic.Ordinary.OrdinaryLeftTensorCongruence
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleTensorTerms

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.BlockTensor
universe u
variable (k L R : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
variable (O : CochainComplex (ModuleCat.{u} (R ⊗[k] Lᵐᵒᵖ)) ℤ)
variable (T : CochainComplex (ModuleCat.{u} (L ⊗[k] Rᵐᵒᵖ)) ℤ)

open BimoduleComplexTensor

def firstTermEquiv (Z : CochainComplex (ModuleCat.{u} L) ℤ) (p q : ℤ) :
    term k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z) p q ≃ₗ[L × R]
      BlockModule.Second k L R (term k R L O Z p q) := by
  let M := OffDiagonal (BimoduleCoefficients k R L (O.X p)) (BimoduleCoefficients k L R (T.X p))
  let eM := RetainedBimodule.rightEquiv k (L × R) (L × R) M
  let eZ : ComplexTensor.leftTerm k (L × R) (BlockModule.firstComplex L R Z) q ≃ₗ[L × R]
      BlockModule.First k L R (ComplexTensor.leftTerm k L Z q) := LinearEquiv.refl _ _
  exact (LeftTensor.congr (k := k) (A := L × R) (S := L × R) eM (RetainedBimodule.rightEquiv_left k (L × R) (L × R) M) eZ).trans
    (FirstBlockTensor.equivalence k L R (BimoduleCoefficients k R L (O.X p))
      (BimoduleCoefficients k L R (T.X p)) (ComplexTensor.leftTerm k L Z q))

def secondTermEquiv (Z : CochainComplex (ModuleCat.{u} R) ℤ) (p q : ℤ) :
    term k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z) p q ≃ₗ[L × R]
      BlockModule.First k L R (term k L R T Z p q) := by
  let M := OffDiagonal (BimoduleCoefficients k R L (O.X p)) (BimoduleCoefficients k L R (T.X p))
  let eM := RetainedBimodule.rightEquiv k (L × R) (L × R) M
  let eZ : ComplexTensor.leftTerm k (L × R) (BlockModule.secondComplex L R Z) q ≃ₗ[L × R]
      BlockModule.Second k L R (ComplexTensor.leftTerm k R Z q) := LinearEquiv.refl _ _
  exact (LeftTensor.congr (k := k) (A := L × R) (S := L × R) eM (RetainedBimodule.rightEquiv_left k (L × R) (L × R) M) eZ).trans
    (SecondBlockTensor.equivalence k L R (BimoduleCoefficients k R L (O.X p))
      (BimoduleCoefficients k L R (T.X p)) (ComplexTensor.leftTerm k R Z q))

theorem firstTermEquiv_map (Z : CochainComplex (ModuleCat.{u} L) ℤ) {p p' q q' : ℤ}
    (fO : O.X p ⟶ O.X p') (fT : T.X p ⟶ T.X p') (g : Z.X q ⟶ Z.X q') :
    (firstTermEquiv k L R O T Z p' q').toLinearMap.comp
      (map k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.firstComplex L R Z)
        (OffDiagonal.objectMap k L R fO fT) ((ProductModules.firstInflation L R).map g)) =
    (BlockModule.secondMap k L R (map k R L O Z fO g)).comp
      (firstTermEquiv k L R O T Z p q).toLinearMap := by
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.ext
  intro x z
  rfl

theorem secondTermEquiv_map (Z : CochainComplex (ModuleCat.{u} R) ℤ) {p p' q q' : ℤ}
    (fO : O.X p ⟶ O.X p') (fT : T.X p ⟶ T.X p') (g : Z.X q ⟶ Z.X q') :
    (secondTermEquiv k L R O T Z p' q').toLinearMap.comp
      (map k (L × R) (L × R) (OffDiagonal.complex k L R O T) (BlockModule.secondComplex L R Z)
        (OffDiagonal.objectMap k L R fO fT) ((ProductModules.secondInflation L R).map g)) =
    (BlockModule.firstMap k L R (map k L R T Z fT g)).comp
      (secondTermEquiv k L R O T Z p q).toLinearMap := by
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.ext
  intro x z
  rfl
end LittleFinitistic.OrdinarySimulation.BlockTensor

end

end OAI
