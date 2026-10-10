import OAI.Algebra.AuslanderReiten.Bar.BarBalancedEquiv

namespace OAI

noncomputable section
namespace ArExplicit.BarBalanced
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
attribute [local instance 2000] AbsoluteBar.baseModule AbsoluteBar.bimoduleTower

def zeroModuleEquiv : ModuleBar.moduleObject k R M 0 ≃ₗ[R] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def zeroEvaluationEquiv : evaluated k R M 0 ≃ₗ[R] M :=
  (equiv k R M 0).trans (zeroModuleEquiv k R M)

@[simp] theorem zeroEvaluationEquiv_tmul (a : bar k R 0) (m : M) :
    zeroEvaluationEquiv k R M (BalancedTensor.tmul a m) = (show R from a.value) • m := rfl

end ArExplicit.BarBalanced

end

end OAI
