import OAI.Algebra.AuslanderReiten.Ext.AExtActions
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorProducts

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q ⊗[k] ArExplicit.T k q))]
local notation "T" => ArExplicit.T k q

theorem aFirst_second_commute :
    type_of% (ModuleBar.tensorCubics_commute k T T (Simple q) (Simple q)
      (CocycleData.p q) (CocycleData.p_isCocycle3 q)
      (CocycleData.p q) (CocycleData.p_isCocycle3 q)) :=
  ModuleBar.tensorCubics_commute k T T (Simple q) (Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)

end ArExplicit.Resolution

end

end OAI
