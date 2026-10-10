import OAI.GroupTheory.PolycyclicRecognition.Algebra.RegularCoefficientAction
import Mathlib.RepresentationTheory.Coinvariants

namespace OAI

/-! # Evaluation pairing with the regular dual

Inverse coefficient action makes evaluation equivariant in the regular-dual
argument and invariant under the diagonal action on the other two arguments.
It therefore descends to coinvariant tensor products.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2200] TensorProduct.instModule
variable {G : Type} [Group G]

private abbrev integralModuleComm {M : Type} [AddCommGroup M]
    (h₁ h₂ : Module ℤ M) :
    @SMulCommClass ℤ ℤ M h₁.toSMul h₂.toSMul :=
  @SMulCommClass.mk ℤ ℤ M h₁.toSMul h₂.toSMul (by
    intro r s x
    exact (show h₁.smul r (h₂.smul s x) = h₂.smul s (h₁.smul r x) from by
      rw [int_smul_eq_zsmul h₁, int_smul_eq_zsmul h₂,
        int_smul_eq_zsmul h₂, int_smul_eq_zsmul h₁]
      rw [smul_smul, smul_smul, mul_comm]))

private def integralLinearMapOfAddHom {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (f : M →+ N) : M →ₗ[ℤ] N where
  __ := f
  map_smul' r x := map_intCast_smul f ℤ ℤ r x

def regularDualEvaluation (P A : Rep ℤ G) (a : A) (p : P) : regularDual P ⟶ A :=
  Rep.ofHom ⟨integralLinearMapOfAddHom {
    toFun := fun f => regularCoefficientAction A (f.hom p) a
    map_zero' := by simp
    map_add' f h := by simp [Rep.add_hom]
    }, by
      intro g
      apply LinearMap.ext
      intro f
      change regularCoefficientAction A ((regularRightTranslation g).hom (f.hom p)) a =
        A.ρ g (regularCoefficientAction A (f.hom p) a)
      rw [regularCoefficientAction_rightTranslation]
      rfl⟩

@[simp] theorem regularDualEvaluation_apply (P A : Rep ℤ G) (a : A) (p : P)
    (f : P ⟶ Rep.leftRegular ℤ G) :
    (regularDualEvaluation P A a p).hom f = regularCoefficientAction A (f.hom p) a := rfl

def regularDualPairingInP (P A : Rep ℤ G) (a : A) : P →ₗ[ℤ] (regularDual P ⟶ A) :=
  integralLinearMapOfAddHom {
    toFun := regularDualEvaluation P A a
    map_zero' := by
      apply Rep.hom_ext
      apply DFunLike.ext
      intro f
      change regularCoefficientAction A (f.hom 0) a = 0
      simp
    map_add' p q := by
      apply Rep.hom_ext
      apply DFunLike.ext
      intro f
      change regularCoefficientAction A (f.hom (p + q)) a =
        regularCoefficientAction A (f.hom p) a + regularCoefficientAction A (f.hom q) a
      simp only [map_add, LinearMap.add_apply]
    }

def regularDualPairing (P A : Rep ℤ G) :=
  let h : Module ℤ (regularDual P ⟶ A) := inferInstance
  letI : Module ℤ (P →ₗ[ℤ] (regularDual P ⟶ A)) :=
    @LinearMap.module ℤ ℤ ℤ P (regularDual P ⟶ A)
      _ _ _ _ _ h (RingHom.id ℤ) _ h (integralModuleComm h h)
  integralLinearMapOfAddHom (M := A) (N := P →ₗ[ℤ] (regularDual P ⟶ A)) ({
  toFun := regularDualPairingInP P A
  map_zero' := by
    apply LinearMap.ext
    intro p
    apply Rep.hom_ext
    apply DFunLike.ext
    intro f
    change regularCoefficientAction A (f.hom p) 0 = 0
    exact map_zero _
  map_add' := fun a b => by
    apply LinearMap.ext
    intro p
    apply Rep.hom_ext
    apply DFunLike.ext
    intro f
    change regularCoefficientAction A (f.hom p) (a + b) =
      regularCoefficientAction A (f.hom p) a + regularCoefficientAction A (f.hom p) b
    exact map_add _ _ _
  } : A →+ (P →ₗ[ℤ] (regularDual P ⟶ A)))

theorem regularDualEvaluation_diagonal (P A : Rep ℤ G) (g : G) (a : A) (p : P) :
    regularDualEvaluation P A (A.ρ g a) (P.ρ g p) = regularDualEvaluation P A a p := by
  apply Rep.hom_ext
  apply DFunLike.ext
  intro f
  change regularCoefficientAction A (f.hom (P.ρ g p)) (A.ρ g a) =
    regularCoefficientAction A (f.hom p) a
  rw [Rep.hom_comm_apply f, regularCoefficientAction_leftTranslation]
  simp only [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul,
    inv_mul_cancel, map_one, Module.End.one_apply]

def regularTensorEvaluation (P A : Rep ℤ G) :
    A ⊗[ℤ] P →ₗ[ℤ] (regularDual P ⟶ A) :=
  TensorProduct.lift (regularDualPairing P A)

theorem regularTensorEvaluation_invariant (P A : Rep ℤ G) (g : G) :
    regularTensorEvaluation P A ∘ₗ (A.ρ.tprod P.ρ) g = regularTensorEvaluation P A := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a p =>
    change regularDualEvaluation P A (A.ρ g a) (P.ρ g p) = regularDualEvaluation P A a p
    exact regularDualEvaluation_diagonal P A g a p
  | add x y hx hy => simp only [map_add, hx, hy]

def regularCoinvariantEvaluation (P A : Rep ℤ G) :
    ((Rep.coinvariantsTensor ℤ G).obj A).obj P →ₗ[ℤ] (regularDual P ⟶ A) :=
  Representation.Coinvariants.lift _ (regularTensorEvaluation P A)
    (regularTensorEvaluation_invariant P A)

@[simp] theorem regularCoinvariantEvaluation_tmul (P A : Rep ℤ G) (a : A) (p : P) :
    regularCoinvariantEvaluation P A (Rep.coinvariantsTensorMk A P a p) =
      regularDualEvaluation P A a p := rfl

end PolycyclicRecognition

end

end OAI
