import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleAssociativity
import OAI.Algebra.Finitistic.Ordinary.OrdinaryLeftTensorCongruence
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleTensorTerms
import OAI.Algebra.Finitistic.Ordinary.OrdinaryMiddleTensorFunctors

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A B N : Type u) [Field k] [Ring S] [Ring A] [Ring B]
  [Algebra k S] [Algebra k A] [Algebra k B]
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
local instance : SMulCommClass Bᵐᵒᵖ A N := ⟨fun b a n => (smul_comm a b n).symm⟩
variable (Q : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} B) ℤ)

abbrev middleBimoduleComplex := ((bimoduleTensorFunctor k S A Bᵐᵒᵖ N).mapHomologicalComplex (.up ℤ)).obj Q

/-- Associativity on actual cochain terms, retaining the outside S-action. -/
def associativeTermEquiv (p q : ℤ) :
    term k S B (middleBimoduleComplex k S A B N Q) Z p q ≃ₗ[S]
      term k S A Q (middleLeftComplex k A B N Z) p q := by
  let eZ : LeftTensor k B A N (ComplexTensor.leftTerm k B Z q) ≃ₗ[A]
      ComplexTensor.leftTerm k A (middleLeftComplex k A B N Z) q := LinearEquiv.refl _ _
  exact (BimoduleAssociativity.equivalence k S A B (BimoduleCoefficients k S A (Q.X p)) N
    (ComplexTensor.leftTerm k B Z q)).trans
    (LeftTensor.congr (LinearEquiv.refl Aᵐᵒᵖ (BimoduleCoefficients k S A (Q.X p))) (fun _ _ => rfl) eZ)

/-- Associativity commutes with both actual cochain-term maps. -/
theorem associativeTermEquiv_map {p p' q q' : ℤ} (f : Q.X p ⟶ Q.X p') (g : Z.X q ⟶ Z.X q') :
    (associativeTermEquiv k S A B N Q Z p' q').toLinearMap.comp
      (map k S B (middleBimoduleComplex k S A B N Q) Z ((bimoduleTensorFunctor k S A Bᵐᵒᵖ N).map f) g) =
    (map k S A Q (middleLeftComplex k A B N Z) f ((middleLeftFunctor k A B N).map g)).comp
      (associativeTermEquiv k S A B N Q Z p q).toLinearMap := by
  let F := (associativeTermEquiv k S A B N Q Z p' q').toLinearMap.comp
    (map k S B (middleBimoduleComplex k S A B N Q) Z ((bimoduleTensorFunctor k S A Bᵐᵒᵖ N).map f) g)
  let G := (map k S A Q (middleLeftComplex k A B N Z) f ((middleLeftFunctor k A B N).map g)).comp
    (associativeTermEquiv k S A B N Q Z p q).toLinearMap
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.ext
  intro x z
  let j := (LeftTensor.mk k S B
    (BimoduleCoefficients k S B ((middleBimoduleComplex k S A B N Q).X p))
    (ComplexTensor.leftTerm k B Z q)).flip z
  let L : BalancedTensor.Tensor k A (BimoduleCoefficients k S A (Q.X p)) N →+
      term k S A Q (middleLeftComplex k A B N Z) p' q' :=
    ((F.restrictScalars k).comp j).toAddMonoidHom
  let R : BalancedTensor.Tensor k A (BimoduleCoefficients k S A (Q.X p)) N →+
      term k S A Q (middleLeftComplex k A B N Z) p' q' :=
    ((G.restrictScalars k).comp j).toAddMonoidHom
  have h : L = R := by
    apply AddMonoidHom.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | hz => exact L.map_zero.trans R.map_zero.symm
    | ht m n => rfl
    | ha x y hx hy =>
      exact (L.map_add x y).trans ((congrArg₂ (· + ·) hx hy).trans (R.map_add x y).symm)
  exact congrArg (fun f => f x) h

end LittleFinitistic.BimoduleComplexTensor

end

end OAI
