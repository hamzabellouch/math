import OAI.Algebra.AuslanderReiten.Evaluation.CanonicalRegularEndpoint

namespace OAI

noncomputable section
namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} R) (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))
variable (f : M ⟶ AbsoluteBar.moduleObject k R 0)

def regularMap : (EnvelopingBimodule.evaluationFunctor k R X).obj M ⟶ X :=
  (EnvelopingBimodule.evaluationFunctor k R X).map f ≫ (nativeEndpointIso k R X).hom

theorem regularMap_tmul (m : EnvelopingBimodule k R M) (x : X) :
    regularMap k R X M f (BalancedTensor.tmul m x) =
      (show R from f m.value) • x := by
  change (nativeEndpointIso k R X).hom
    (BalancedTensor.tmul (EnvelopingBimodule.map f m) x) = _
  rw [nativeEndpointIso_tmul_value]
  rfl

end ArExplicit.BarBalanced

end

end OAI
