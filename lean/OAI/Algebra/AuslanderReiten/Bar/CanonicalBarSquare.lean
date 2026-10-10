import OAI.Algebra.AuslanderReiten.Bar.BarBalancedCanonical
import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingEvaluationFunctor

namespace OAI

noncomputable section
namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} R)

theorem canonical_square {m n : ℕ}
    (f : AbsoluteBar.moduleObject k R m ⟶ AbsoluteBar.moduleObject k R n)
    (g : ModuleBar.moduleObject k R X m ⟶ ModuleBar.moduleObject k R X n)
    (h : ∀ z, canonicalEquiv k R X n (canonicalMap k R X f z) =
      g (canonicalEquiv k R X m z)) :
    (EnvelopingBimodule.evaluationFunctor k R X).map f ≫
        (canonicalEquiv k R X n).toModuleIso.hom =
      (canonicalEquiv k R X m).toModuleIso.hom ≫ g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact h z

end ArExplicit.BarBalanced

end

end OAI
