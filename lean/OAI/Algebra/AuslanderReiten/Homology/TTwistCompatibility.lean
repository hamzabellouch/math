import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTwistCocycle

namespace OAI

noncomputable section
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] (q : k) (H : kˣ)

theorem inverseTwist_cubic_compatible (a b d : T k q) (m : Resolution.Simple q) :
    CocycleData.p q ((TrivialExtension.twist H).symm a)
      ((TrivialExtension.twist H).symm b) ((TrivialExtension.twist H).symm d) •
        (LinearEquiv.refl k (Resolution.Simple q)) m =
      ((H⁻¹ : kˣ) : k) • (LinearEquiv.refl k (Resolution.Simple q))
        (CocycleData.p q a b d • m) := by
  simp only [LinearEquiv.refl_apply]
  exact p_inverse_twist_simple q H a b d m

end ArExplicit.T

end

end OAI
