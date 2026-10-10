import OAI.Algebra.AuslanderReiten.Bar.CanonicalBarEvaluation

namespace OAI

noncomputable section
namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R] [charP : CharP k 2]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} R)

theorem canonicalTermIso_hom_eq (n : ℕ) :
    (canonicalTermIso k R X n).hom =
      ModuleCat.ofHom (canonicalEquiv k R X (n+1)).toLinearMap := rfl

private abbrev canonicalTermTmulProof (n : ℕ)
    (z : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R (n+1))) (x : X) :=
  canonicalEquiv_tmul k R X (n+1) z x

omit charP in
/- The characteristic assumption is retained explicitly in the complex-isomorphism interface.
Using its defining linear equivalence avoids expanding the complex module structures. -/
theorem canonicalTermIso_tmul [CharP k 2] (n : ℕ)
    (z : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R (n+1))) (x : X) :
    type_of% (canonicalTermTmulProof k R X n z x) :=
  canonicalTermTmulProof k R X n z x

include charP in
theorem canonicalComplexIso_tmul (n : ℕ)
    (z : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R (n+1))) (x : X) :
    type_of% (canonicalTermIso_tmul k R X n z x) :=
  canonicalTermIso_tmul k R X n z x

end ArExplicit.BarBalanced

end

end OAI
