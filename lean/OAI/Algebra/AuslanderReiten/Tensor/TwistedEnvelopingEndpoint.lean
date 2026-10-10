import OAI.Algebra.AuslanderReiten.Tensor.TwistedEnvelopingFunctor

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (σ : R ≃ₐ[k] R) (M N : ModuleCat.{u} R)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

theorem twistedEnvelopingEndpoint_tmul
    (e : (ModuleCat.restrictScalars σ.symm.toRingHom).obj M ≅ N)
    (a : EnvelopingBimodule k R (twistedFiniteModule σ).carrier) (m : M) :
    (((twistedEnvelopingRestrictionIso σ).app M) ≪≫ e).hom.hom
      (BalancedTensor.tmul a m) = e.hom.hom (σ.symm a.value.value • m) := rfl

end ArExplicit

end

end OAI
