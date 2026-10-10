import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorNative

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.BalancedTensor
universe u
variable {k R S F : Type u} [Field k] [Ring R] [Ring S] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module S F]
variable [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable (M : Type u) [AddCommGroup M] [Module R M] [mM : Module k M] [IsScalarTower k R M]
variable {N : ModuleCat.{u} S} (e : BalancedTensor k R F M ≃ₗ[S] N)

def tensorEvaluationIso :
    (functor (k := k) (R := R) (S := S) (F := F)).obj (ModuleCat.of R M) ≅ N :=
  nativeObjectIso (k := k) (R := R) (S := S) (F := F) M ≪≫ e.toModuleIso

theorem tensorEvaluationIso_tmul (f : F) (m : M) :
    (tensorEvaluationIso M e).hom.hom
      (letI := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
       tmul f m) = e (tmul f m) :=
  congrArg e (nativeObjectIso_tmul M f m)

end ArExplicit.BalancedTensor

end

end OAI
