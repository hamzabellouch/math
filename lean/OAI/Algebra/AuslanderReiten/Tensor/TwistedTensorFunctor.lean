import OAI.Algebra.AuslanderReiten.Tensor.TwistedTensor
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorCategory
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.TwistedBimodule
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (σ : R ≃ₐ[k] R)

def leftModuleCoordinates (M : ModuleCat.{u} R) :
    TwistedLeftModule k R σ M ≃ₗ[R]
      (ModuleCat.restrictScalars σ.symm.toRingHom).obj M where
  toFun x := x.value
  invFun x := ⟨x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def tensorRestrictionEquiv (M : ModuleCat.{u} R) :
    BalancedTensor k R (TwistedBimodule k R σ) M ≃ₗ[R]
      (ModuleCat.restrictScalars σ.symm.toRingHom).obj M :=
  (tensorUntwist σ).trans (leftModuleCoordinates σ M)

@[simp] theorem tensorRestrictionEquiv_tmul (M : ModuleCat.{u} R)
    (a : TwistedBimodule k R σ) (m : M) :
    tensorRestrictionEquiv σ M (BalancedTensor.tmul a m) = σ.symm a.value • m := rfl

def tensorRestrictionIso :
    BalancedTensor.functor (k := k) (R := R) (S := R) (F := TwistedBimodule k R σ) ≅
      ModuleCat.restrictScalars σ.symm.toRingHom :=
  NatIso.ofComponents (fun M => (tensorRestrictionEquiv σ M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply BalancedTensor.leftHom_ext
    intro a m
    change σ.symm a.value • f.hom m = f.hom (σ.symm a.value • m)
    exact (f.hom.map_smul _ _).symm)

end ArExplicit.TwistedBimodule

end

end OAI
