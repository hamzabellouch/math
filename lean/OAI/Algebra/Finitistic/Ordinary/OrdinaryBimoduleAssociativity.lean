import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleTensorFunctor
import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorRightRestriction
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBalancedAssociativity
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBalancedCongruence
import OAI.Algebra.Finitistic.Ordinary.OrdinaryLeftTensorMaps

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleAssociativity
universe u
variable (k S A B M N Z : Type u) [Field k] [Ring S] [Ring A] [Ring B]
  [Algebra k S] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [Module k M] [Module S M] [Module Aᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Aᵐᵒᵖ M] [SMulCommClass S Aᵐᵒᵖ M]
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
variable [AddCommGroup Z] [Module k Z] [Module B Z] [IsScalarTower k B Z]
local instance : SMulCommClass Bᵐᵒᵖ A N := ⟨fun b a n => (smul_comm a b n).symm⟩

abbrev coefficient := BimoduleCoefficients k S B
  (ModuleCat.of (S ⊗[k] Bᵐᵒᵖ) (TwoSidedTensor k A S Bᵐᵒᵖ M N))
abbrev source := LeftTensor k B S (coefficient k S A B M N) Z
abbrev target := LeftTensor k A S M (LeftTensor k B A N Z)

def scalarEquiv : source k S A B M N Z ≃ₗ[k] target k S A B M N Z := by
  let e : coefficient k S A B M N ≃ₗ[Bᵐᵒᵖ] RightTensor k A B M N :=
    (TwoSidedTensor.rightActionEquiv k A B S M N).symm
  exact (BalancedTensor.congr (k := k) e (LinearEquiv.refl B Z)).trans
    (BalancedAssociativity.equivalence k A B M N Z)

@[simp] theorem scalarEquiv_mk (m : M) (n : N) (z : Z) :
    scalarEquiv k S A B M N Z (LeftTensor.mk k S B (coefficient k S A B M N) Z
      (TwoSidedTensor.mk k A S Bᵐᵒᵖ M N m n) z) =
    LeftTensor.mk k S A M (LeftTensor k B A N Z) m (LeftTensor.mk k A B N Z n z) := rfl

theorem coefficient_smul_mk (s : S) (m : M) (n : N) :
    s • (show coefficient k S A B M N from TwoSidedTensor.mk k A S Bᵐᵒᵖ M N m n) =
    (show coefficient k S A B M N from TwoSidedTensor.mk k A S Bᵐᵒᵖ M N (s • m) n) := by
  change (s ⊗ₜ[k] (1:Bᵐᵒᵖ)) • TwoSidedTensor.mk k A S Bᵐᵒᵖ M N m n = _
  rw [TwoSidedTensor.tmul_smul_mk,one_smul]

private theorem scalarEquiv_smul_mk (s : S) (m : M) (n : N) (z : Z) :
    scalarEquiv k S A B M N Z
        (s • LeftTensor.mk k S B (coefficient k S A B M N) Z
          (show coefficient k S A B M N from TwoSidedTensor.mk k A S Bᵐᵒᵖ M N m n) z) =
      s • scalarEquiv k S A B M N Z
        (LeftTensor.mk k S B (coefficient k S A B M N) Z
          (show coefficient k S A B M N from TwoSidedTensor.mk k A S Bᵐᵒᵖ M N m n) z) := by
  erw [LeftTensor.smul_mk, coefficient_smul_mk]
  exact (scalarEquiv_mk k S A B M N Z (s • m) n z).trans
    ((LeftTensor.smul_mk k S A M (LeftTensor k B A N Z) s m
      (LeftTensor.mk k A B N Z n z)).symm.trans
        (congrArg (fun y => s • y) (scalarEquiv_mk k S A B M N Z m n z).symm))

/-- Ordinary balanced associativity retains the actual outside left action. -/
def equivalence : source k S A B M N Z ≃ₗ[S] target k S A B M N Z where
  __ := (scalarEquiv k S A B M N Z).toAddEquiv
  map_smul' s x := by
    let e := (scalarEquiv k S A B M N Z).toLinearMap
    let L := e.comp (LeftTensor.action k S B (coefficient k S A B M N) Z s)
    let R := (LeftTensor.action k S A M (LeftTensor k B A N Z) s).comp e
    have h : L = R := by
      apply BalancedTensor.ext
      intro y z
      let Lz : BalancedTensor.Tensor k A M N →+ target k S A B M N Z :=
        (L.comp ((LeftTensor.mk k S B (coefficient k S A B M N) Z).flip z)).toAddMonoidHom
      let Rz : BalancedTensor.Tensor k A M N →+ target k S A B M N Z :=
        (R.comp ((LeftTensor.mk k S B (coefficient k S A B M N) Z).flip z)).toAddMonoidHom
      have hz : Lz = Rz := by
        apply AddMonoidHom.ext
        intro y
        induction y using BalancedTensor.induction_on with
        | hz => exact Lz.map_zero.trans Rz.map_zero.symm
        | ha x y hx hy =>
          exact (Lz.map_add x y).trans ((congrArg₂ (· + ·) hx hy).trans (Rz.map_add x y).symm)
        | ht m n => exact scalarEquiv_smul_mk k S A B M N Z s m n z
      exact congrArg (fun f => f y) hz
    exact congrArg (fun f => f x) h

end LittleFinitistic.BimoduleAssociativity

end

end OAI
