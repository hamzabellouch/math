import OAI.Algebra.AuslanderReiten.Bar.ModuleBarNative
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarExtTwist

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [CharP k 2]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)

def nativeHomTransport :
    ExternalTensor.canonicalHomCochain k R (nativeResolution k R M).complex (ModuleCat.of R M) ⟶
      ExternalTensor.canonicalHomCochain k R (nativeResolution k R M).complex (ModuleCat.of R M) :=
  canonicalHomTransport k R M h e he

theorem nativeHomTransport_ext (n : ℕ) :
    ExternalTensor.homCochainEndExt k R (nativeResolution k R M)
      (nativeHomTransport k R M h e he) n = twistExtAction k R M h e he n := rfl

theorem nativeHomTransport_apply (n : ℕ)
    (f : (nativeResolution k R M).complex.X n →ₗ[R] ModuleCat.of R M)
    (x : (nativeResolution k R M).complex.X n) :
    (show (nativeResolution k R M).complex.X n →ₗ[R] ModuleCat.of R M from
      ((nativeHomTransport k R M h e he).f n).hom f) x =
      e.symm (f (transport k R M h e (n+1) x)) := rfl

end ArExplicit.ModuleBar

end

end OAI
