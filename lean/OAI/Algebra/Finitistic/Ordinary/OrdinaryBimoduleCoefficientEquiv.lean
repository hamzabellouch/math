import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleCoefficients
import OAI.Algebra.Finitistic.Ordinary.OrdinaryLeftTensorCongruence
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleTensorTerms

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleCoefficients
universe u
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable {M N : ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)}

def equiv (e : M ≅ N) : BimoduleCoefficients k S A M ≃ₗ[Aᵐᵒᵖ] BimoduleCoefficients k S A N where
  __ := map k S A e.hom
  invFun := map k S A e.inv
  left_inv x := congrArg (fun h => h.hom x) e.hom_inv_id
  right_inv x := congrArg (fun h => h.hom x) e.inv_hom_id

theorem equiv_left (e : M ≅ N) (s : S) (x : BimoduleCoefficients k S A M) :
    equiv k S A e (s • x) = s • equiv k S A e x := map_left k S A e.hom s x
end LittleFinitistic.BimoduleCoefficients
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable {Q Q' : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ}
variable (e : Q ≅ Q') (Z : CochainComplex (ModuleCat.{u} A) ℤ)

def rightTermEquiv (p q : ℤ) : term k S A Q Z p q ≃ₗ[S] term k S A Q' Z p q :=
  LeftTensor.congr (BimoduleCoefficients.equiv k S A ((HomologicalComplex.eval _ _ p).mapIso e))
    (BimoduleCoefficients.equiv_left k S A ((HomologicalComplex.eval _ _ p).mapIso e))
    (LinearEquiv.refl A (ComplexTensor.leftTerm k A Z q))

/-- Both actual tensor maps respect an isomorphism of genuine bimodule complexes. -/
theorem rightTermEquiv_map (p p' q q' : ℤ) (g : Z.X q ⟶ Z.X q') :
    (rightTermEquiv k S A e Z p' q').toLinearMap.comp (map k S A Q Z (Q.d p p') g) =
    (map k S A Q' Z (Q'.d p p') g).comp (rightTermEquiv k S A e Z p q).toLinearMap := by
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.ext
  intro x z
  exact congrArg (fun y => LeftTensor.mk k S A (BimoduleCoefficients k S A (Q'.X p'))
      (ComplexTensor.leftTerm k A Z q') y (g.hom z))
    (congrArg (fun f => f.hom x) (e.hom.comm p p')).symm

theorem rightTermEquiv_map_id (p q q' : ℤ) (g : Z.X q ⟶ Z.X q') :
    (rightTermEquiv k S A e Z p q').toLinearMap.comp (map k S A Q Z (𝟙 (Q.X p)) g) =
    (map k S A Q' Z (𝟙 (Q'.X p)) g).comp (rightTermEquiv k S A e Z p q).toLinearMap := by
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.ext
  intro x z
  rfl
end LittleFinitistic.BimoduleComplexTensor

end

end OAI
