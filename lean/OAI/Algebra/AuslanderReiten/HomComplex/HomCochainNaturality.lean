import OAI.Algebra.AuslanderReiten.Homology.CochainCycleClass

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X)

theorem homCochainCycleClass_eq_literal (n : ℕ)
    (f : LinearMap.ker (homShort k R (Y := Y) P n).g.hom) :
    homCochainCycleClass k R P n f =
      VectorCochain.literalClass k (homCochain k R P.complex Y) n f := by
  exact (VectorCochain.literalClass_eq_quotient k (homCochain k R P.complex Y) n f).symm

variable (F : homCochain k R P.complex Y ⟶ homCochain k R P.complex Y)

def homCochainEndExt (n : ℕ) : Ext X Y n →ₗ[k] Ext X Y n :=
  (homCochainExtEquiv k R P n).toLinearMap.comp
    ((homologyMap F n).hom.comp (homCochainExtEquiv k R P n).symm.toLinearMap)

theorem homCochainEndExt_cycleClass (n : ℕ)
    (f g : LinearMap.ker (homShort k R (Y := Y) P n).g.hom)
    (hfg : (F.f n).hom f.val = g.val) :
    homCochainEndExt k R P F n
      (P.extMk (ModuleCat.ofHom (X := P.complex.X n) (Y := Y) f.val)
        (n+1) rfl (homCycle_closed k R P n f)) =
      P.extMk (ModuleCat.ofHom (X := P.complex.X n) (Y := Y) g.val)
        (n+1) rfl (homCycle_closed k R P n g) := by
  rw [← homCochainExtEquiv_cycleClass k R P n f,
    ← homCochainExtEquiv_cycleClass k R P n g]
  change (homCochainExtEquiv k R P n)
    ((homologyMap F n).hom ((homCochainExtEquiv k R P n).symm
      ((homCochainExtEquiv k R P n) (homCochainCycleClass k R P n f)))) = _
  rw [LinearEquiv.symm_apply_apply, homCochainCycleClass_eq_literal,
    homCochainCycleClass_eq_literal]
  exact congrArg (homCochainExtEquiv k R P n)
    (VectorCochain.literalClass_map k F n f g hfg)

end ArExplicit.ExternalTensor

end

end OAI
