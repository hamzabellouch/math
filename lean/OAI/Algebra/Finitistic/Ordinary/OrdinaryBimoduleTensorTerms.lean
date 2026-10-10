import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleCoefficients
import OAI.Algebra.Finitistic.Ordinary.OrdinaryLeftTensorMaps
import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorFiniteMatrix
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBalancedCongruence

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} A) ℤ)

abbrev rightComplex : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ :=
  ((ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight (R := k) (A := S) (B := Aᵐᵒᵖ)).toRingHom).mapHomologicalComplex (.up ℤ)).obj Q

abbrev term (p q : ℤ) := LeftTensor k A S (BimoduleCoefficients k S A (Q.X p)) (ComplexTensor.leftTerm k A Z q)

/-- Both actual term maps with the outside left action retained. -/
def map {p p' q q' : ℤ} (f : Q.X p ⟶ Q.X p') (g : Z.X q ⟶ Z.X q') :
    term k S A Q Z p q →ₗ[S] term k S A Q Z p' q' :=
  LeftTensor.bimap (BimoduleCoefficients.map k S A f) (BimoduleCoefficients.map_left k S A f) g.hom

/-- Forgetting the outside action gives exactly the previous balanced tensor term. -/
def forgetEquiv (p q : ℤ) : term k S A Q Z p q ≃ₗ[k]
    ComplexTensor.term k A (rightComplex k S A Q) Z p q := by
  let e : BimoduleCoefficients k S A (Q.X p) ≃ₗ[Aᵐᵒᵖ]
      ComplexTensor.rightTerm k A (rightComplex k S A Q) p := LinearEquiv.refl _ _
  exact BalancedTensor.congr (k := k) e (LinearEquiv.refl A (ComplexTensor.leftTerm k A Z q))

/-- The retained-action map has precisely the same underlying balanced map. -/
theorem forget_map {p p' q q' : ℤ} (f : Q.X p ⟶ Q.X p') (g : Z.X q ⟶ Z.X q') :
    (forgetEquiv k S A Q Z p' q').toLinearMap.comp ((map k S A Q Z f g).restrictScalars k) =
      (ComplexTensor.map k A (rightComplex k S A Q) Z
        ((ModuleCat.restrictScalars (Algebra.TensorProduct.includeRight (R := k) (A := S) (B := Aᵐᵒᵖ)).toRingHom).map f) g).comp
        (forgetEquiv k S A Q Z p q).toLinearMap := by
  apply BalancedTensor.ext
  intro x y
  rfl
end LittleFinitistic.BimoduleComplexTensor

end

end OAI
