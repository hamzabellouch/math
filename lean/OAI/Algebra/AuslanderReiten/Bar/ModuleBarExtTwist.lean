import OAI.Algebra.AuslanderReiten.Bar.ModuleBarHomTwist
import OAI.Algebra.AuslanderReiten.HomComplex.HomCochainNaturality

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable [CharP k 2]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)

def twistExtAction (n : ℕ) :
    Ext (moduleObject k R M 0) (ModuleCat.of R M) n →ₗ[k]
      Ext (moduleObject k R M 0) (ModuleCat.of R M) n :=
  ExternalTensor.homCochainEndExt k R (resolution k R M)
    (canonicalHomTransport k R M h e he) n

theorem twistExtAction_cycle (n : ℕ)
    (f g : LinearMap.ker
      (ExternalTensor.homShort k R (Y := ModuleCat.of R M) (resolution k R M) n).g.hom)
    (hfg : ∀ x : moduleObject k R M (n+1),
      (show moduleObject k R M (n+1) →ₗ[R] M from g.val) x =
        e.symm ((show moduleObject k R M (n+1) →ₗ[R] M from f.val)
          (transport k R M h e (n+1) x))) :
    twistExtAction k R M h e he n
      (ExternalTensor.homCyclesToExt k R (resolution k R M) n f) =
        ExternalTensor.homCyclesToExt k R (resolution k R M) n g := by
  apply ExternalTensor.homCochainEndExt_cycleClass k R (resolution k R M)
    (canonicalHomTransport k R M h e he) n f g
  apply LinearMap.ext
  intro x
  exact (hfg x).symm

end ArExplicit.ModuleBar

end

end OAI
