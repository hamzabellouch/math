import OAI.Algebra.AuslanderReiten.Coordinates.TensorRestriction
import Mathlib.Algebra.Module.TransferInstance

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory
open scoped TensorProduct

universe u

@[ext] structure EnvelopingBimodule (k R : Type u) [Field k] [Ring R] [Algebra k R]
    (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)) where
  value : M

namespace EnvelopingBimodule

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))

def coordinates : EnvelopingBimodule k R M ≃ M where
  toFun := value
  invFun := EnvelopingBimodule.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (EnvelopingBimodule k R M) := (coordinates M).addCommGroup
instance : Module (R ⊗[k] Rᵐᵒᵖ) (EnvelopingBimodule k R M) :=
  (coordinates M).addEquiv.module (R ⊗[k] Rᵐᵒᵖ)
instance : Module R (EnvelopingBimodule k R M) :=
  Module.compHom _ (tensorLeftInclusion k R Rᵐᵒᵖ)
instance : Module Rᵐᵒᵖ (EnvelopingBimodule k R M) :=
  Module.compHom _ (tensorRightInclusion k R Rᵐᵒᵖ)

@[simp] theorem value_zero : (0 : EnvelopingBimodule k R M).value = 0 := rfl
@[simp] theorem value_add (x y : EnvelopingBimodule k R M) :
    (x + y).value = x.value + y.value := rfl
@[simp] theorem value_smul (a : R ⊗[k] Rᵐᵒᵖ) (x : EnvelopingBimodule k R M) :
    (a • x).value = a • x.value := rfl
@[simp] theorem value_left_smul (a : R) (x : EnvelopingBimodule k R M) :
    (a • x).value = (a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) • x.value := rfl
@[simp] theorem value_right_smul (b : Rᵐᵒᵖ) (x : EnvelopingBimodule k R M) :
    (b • x).value = ((1 : R) ⊗ₜ[k] b) • x.value := rfl

instance : SMulCommClass R Rᵐᵒᵖ (EnvelopingBimodule k R M) where
  smul_comm a b x := by
    ext
    change (a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) • (((1 : R) ⊗ₜ[k] b) • x.value) =
      ((1 : R) ⊗ₜ[k] b) • ((a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) • x.value)
    simp only [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

def leftEquiv : EnvelopingBimodule k R M ≃ₗ[R]
    ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj M) where
  __ := coordinates M
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rightEquiv : EnvelopingBimodule k R M ≃ₗ[Rᵐᵒᵖ]
    ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj M) where
  __ := coordinates M
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance [Module.Projective R ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj M)] :
    Module.Projective R (EnvelopingBimodule k R M) :=
  Module.Projective.of_equiv (leftEquiv M).symm

instance [Module.Projective Rᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj M)] :
    Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R M) :=
  Module.Projective.of_equiv (rightEquiv M).symm

instance [Module.Finite R ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj M)] :
    Module.Finite R (EnvelopingBimodule k R M) :=
  Module.Finite.equiv (leftEquiv M).symm

instance [Module.Finite Rᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj M)] :
    Module.Finite Rᵐᵒᵖ (EnvelopingBimodule k R M) :=
  Module.Finite.equiv (rightEquiv M).symm

variable [Module k M]

instance : Module k (EnvelopingBimodule k R M) := (coordinates M).addEquiv.module k

@[simp] theorem value_scalar_smul (a : k) (x : EnvelopingBimodule k R M) :
    (a • x).value = a • x.value := rfl

def scalarEquiv : EnvelopingBimodule k R M ≃ₗ[k] M := (coordinates M).addEquiv.linearEquiv k

instance [Module.Finite k M] : Module.Finite k (EnvelopingBimodule k R M) :=
  Module.Finite.equiv (scalarEquiv M).symm

variable [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]

instance : IsScalarTower k R (EnvelopingBimodule k R M) :=
  IsScalarTower.of_algebraMap_smul fun a x => by
    ext
    change ((algebraMap k R a) ⊗ₜ[k] (1 : Rᵐᵒᵖ)) • x.value = a • x.value
    exact IsScalarTower.algebraMap_smul (R ⊗[k] Rᵐᵒᵖ) a x.value

instance : IsScalarTower k Rᵐᵒᵖ (EnvelopingBimodule k R M) :=
  IsScalarTower.of_algebraMap_smul fun a x => by
    ext
    change ((1 : R) ⊗ₜ[k] (algebraMap k Rᵐᵒᵖ a)) • x.value = a • x.value
    rw [show (1 : R) ⊗ₜ[k] algebraMap k Rᵐᵒᵖ a = algebraMap k (R ⊗[k] Rᵐᵒᵖ) a from
      (Algebra.TensorProduct.includeRight : Rᵐᵒᵖ →ₐ[k] R ⊗[k] Rᵐᵒᵖ).commutes a]
    exact IsScalarTower.algebraMap_smul (R ⊗[k] Rᵐᵒᵖ) a x.value

instance : SMulCommClass k R (EnvelopingBimodule k R M) where
  smul_comm a r x := by
    simp only [← IsScalarTower.algebraMap_smul R a, ← mul_smul, Algebra.commutes]

instance : SMulCommClass k Rᵐᵒᵖ (EnvelopingBimodule k R M) where
  smul_comm a r x := by
    simp only [← IsScalarTower.algebraMap_smul Rᵐᵒᵖ a, ← mul_smul, Algebra.commutes]

end EnvelopingBimodule
end ArExplicit

end

end OAI
