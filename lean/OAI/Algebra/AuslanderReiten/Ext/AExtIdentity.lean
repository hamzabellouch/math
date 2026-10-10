import OAI.Algebra.AuslanderReiten.Ext.AExtPolynomial
import OAI.Algebra.AuslanderReiten.Ext.TTensorActions
import OAI.Algebra.AuslanderReiten.Ext.TTensorIdentity
import OAI.Algebra.AuslanderReiten.Ext.ExtKunnethIdentity
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorScalarProducts

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q ⊗[k] ArExplicit.T k q))]
local notation "T" => ArExplicit.T k q
local notation "S" => ModuleCat.of T (Simple q)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

theorem aExtKunneth_identity :
    type_of% (ModuleBar.tensorKunneth_identity k T T (Simple q) (Simple q)) :=
  ModuleBar.tensorKunneth_identity k T T (Simple q) (Simple q)

variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : NoPositivePowerOne q)

theorem aExtCoefficient_identity :
    type_of% ((congrArg (tTensorCoefficientEquiv q hq hq1 h 0)
      (aExtKunneth_identity q)).trans (tTensorCoefficient_identity q hq hq1 h)) :=
  (congrArg (tTensorCoefficientEquiv q hq hq1 h 0)
    (aExtKunneth_identity q)).trans (tTensorCoefficient_identity q hq hq1 h)

end ArExplicit.Resolution

end

end OAI
