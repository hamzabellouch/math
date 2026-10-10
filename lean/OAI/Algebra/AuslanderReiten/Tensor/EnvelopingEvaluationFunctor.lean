import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingBalancedMap
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

namespace OAI

noncomputable section
namespace ArExplicit.EnvelopingBimodule
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
variable (X : ModuleCat.{u} R) [Module k X] [IsScalarTower k R X]

def evaluationFunctor : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ) ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (BalancedTensor k R (EnvelopingBimodule k R M) X)
  map f := ModuleCat.ofHom (tensorMap X f)
  map_id M := by apply ModuleCat.hom_ext; exact tensorMap_id X
  map_comp f g := by apply ModuleCat.hom_ext; exact tensorMap_comp X f g

instance : (evaluationFunctor k R X).Additive where
  map_add := by intro M N f g; apply ModuleCat.hom_ext; exact tensorMap_add X f g

omit [IsScalarTower k R X] in
@[simp] theorem evaluationFunctor_map_tmul
    {M N : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)} (f : M ⟶ N)
    (m : EnvelopingBimodule k R M) (x : X) :
    (evaluationFunctor k R X).map f (BalancedTensor.tmul m x) =
      BalancedTensor.tmul (map f m) x := rfl

end ArExplicit.EnvelopingBimodule

end

end OAI
