import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorMapEquiv
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorScalar

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.BalancedTensor
universe u
variable {k R S F : Type u} [Field k] [Ring R] [Ring S] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module S F]
variable [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable (M : Type u) [AddCommGroup M] [Module R M] [mM : Module k M] [IsScalarTower k R M]

theorem nativeObject_eq :
    (functor (k := k) (R := R) (S := S) (F := F)).obj (ModuleCat.of R M) =
      ModuleCat.of S (BalancedTensor k R F M) := by
  cases ExternalTensor.canonicalScalar_eq k R M (mM := mM)
  rfl

def nativeObjectIso :
    (functor (k := k) (R := R) (S := S) (F := F)).obj (ModuleCat.of R M) ≅
      ModuleCat.of S (BalancedTensor k R F M) :=
  eqToIso (nativeObject_eq (k := k) (R := R) (S := S) (F := F) M)

theorem nativeObjectIso_tmul (f : F) (m : M) :
    (nativeObjectIso (k := k) (R := R) (S := S) (F := F) M).hom.hom
      (letI := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
       tmul f m) = tmul f m := by
  cases ExternalTensor.canonicalScalar_eq k R M (mM := mM)
  rfl

variable {M}
variable {L : Type u} [AddCommGroup L] [Module R L] [mL : Module k L] [IsScalarTower k R L]

theorem nativeObjectIso_natural (f : M →ₗ[R] L) :
    (functor (k := k) (R := R) (S := S) (F := F)).map (ModuleCat.ofHom f) ≫
        (nativeObjectIso (k := k) (R := R) (S := S) (F := F) L).hom =
      (nativeObjectIso (k := k) (R := R) (S := S) (F := F) M).hom ≫
        ModuleCat.ofHom (mapRight (k := k) (F := F) (S := S) f) := by
  cases ExternalTensor.canonicalScalar_eq k R M (mM := mM)
  cases ExternalTensor.canonicalScalar_eq k R L (mM := mL)
  rfl

end ArExplicit.BalancedTensor

end

end OAI
