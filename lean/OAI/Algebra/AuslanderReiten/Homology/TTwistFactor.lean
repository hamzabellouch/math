import OAI.Algebra.AuslanderReiten.Ext.TTwistExtPolynomial

namespace OAI

noncomputable section
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)

theorem tInverseTwistExt_factor (n : ℕ) :
    ModuleBar.twistExtAction k (ArExplicit.T k q) (Simple q) (TrivialExtension.twist H).symm
      (LinearEquiv.refl k _) (ArExplicit.T.inverseTwist_simple_compatible q H) n =
      tInverseTwistExt q H n := rfl

end ArExplicit.Resolution

end

end OAI
