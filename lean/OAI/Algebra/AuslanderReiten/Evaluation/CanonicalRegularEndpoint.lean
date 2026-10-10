import OAI.Algebra.AuslanderReiten.Bar.NativeBarAugmentation

namespace OAI

noncomputable section
namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} R)

@[simp] theorem nativeEndpointIso_tmul_value
    (m : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R 0)) (x : X) :
    (nativeEndpointIso k R X).hom (BalancedTensor.tmul m x) = (show R from m.value) • x := by
  change canonicalEquiv k R X 0 (BalancedTensor.tmul m x) = _
  rw [canonicalEquiv_tmul]
  rfl

end ArExplicit.BarBalanced

end

end OAI
