import OAI.Algebra.AuslanderReiten.HomComplex.HomCochainExt

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X)

def homCochainQuotientEquiv (n : ℕ) :
    (homCochain k R P.complex Y).homology n ≃ₗ[k]
      (LinearMap.ker (homShort k R (Y := Y) P n).g.hom ⧸
        LinearMap.range (homShort k R (Y := Y) P n).moduleCatToCycles) :=
  ((homCochain k R P.complex Y).homologyIsoSc' (n-1) n (n+1)
    (by cases n <;> simp) (by simp)).toLinearEquiv.trans
      (homShort k R (Y := Y) P n).moduleCatHomologyIso.toLinearEquiv

def homCochainCycleClass (n : ℕ)
    (f : LinearMap.ker (homShort k R (Y := Y) P n).g.hom) :
    (homCochain k R P.complex Y).homology n :=
  (homCochainQuotientEquiv k R P n).symm (Submodule.Quotient.mk f)

theorem homCochainExtEquiv_cycleClass (n : ℕ)
    (f : LinearMap.ker (homShort k R (Y := Y) P n).g.hom) :
    homCochainExtEquiv k R P n (homCochainCycleClass k R P n f) =
      P.extMk (ModuleCat.ofHom (X := P.complex.X n) (Y := Y) f.val)
        (n+1) rfl (homCycle_closed k R P n f) := by
  change ((Submodule.quotEquivOfEq _ _ (homCyclesToExt_kernel k R P n).symm).trans
      ((homCyclesToExt k R P n).quotKerEquivOfSurjective
        (homCyclesToExt_surjective k R P n)))
    ((homCochainQuotientEquiv k R P n)
      ((homCochainQuotientEquiv k R P n).symm (Submodule.Quotient.mk f))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end ArExplicit.ExternalTensor

end

end OAI
