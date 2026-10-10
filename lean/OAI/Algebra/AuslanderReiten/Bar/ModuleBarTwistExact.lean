import OAI.Algebra.AuslanderReiten.Bar.ModuleBarNativeTransport
import OAI.Algebra.AuslanderReiten.Resolutions.MapResolutionExtConjugate

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [CharP k 2]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

local instance restrictionEquivalence : (ModuleCat.restrictScalars h.toRingHom).IsEquivalence :=
  ModuleCat.restrictScalars_isEquivalence_of_ringEquiv h.toRingEquiv

def nativeTransportResolutionHom :
    ProjectiveResolution.Hom (nativeResolution k R M)
      (ResolutionProducts.mapResolution (ModuleCat.restrictScalars h.toRingHom) (nativeResolution k R M))
      (nativeEndpointIso k R M h e he).hom where
  hom := (nativeTransportIso k R M h e he).hom
  hom_f_zero_comp_π_f_zero := by
    rw [ResolutionProducts.mapResolution_π_zero, ChainComplex.single₀_map_f_zero]
    exact nativeTransport_augmentation k R M h e he

theorem twistExtAction_eq_exactFunctor (n : ℕ)
    (x : Ext (ModuleCat.of R M) (ModuleCat.of R M) n) :
    twistExtAction k R M h e he n x =
      ((Ext.mk₀ (nativeEndpointIso k R M h e he).hom).comp
        (x.mapExactFunctor (ModuleCat.restrictScalars h.toRingHom)) (zero_add n)).comp
          (Ext.mk₀ (nativeEndpointIso k R M h e he).inv) (add_zero n) := by
  let P := nativeResolution k R M
  let H := nativeHomTransport k R M h e he
  obtain ⟨f, rfl⟩ := ExternalTensor.homCyclesToExt_surjective k R P n x
  have hg : (ExternalTensor.homShort k R (Y := ModuleCat.of R M) P n).g.hom
      ((H.f n).hom f.val) = 0 := by
    have hh := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (H.comm n (n+1))) f.val
    change (ExternalTensor.homShort k R (Y := ModuleCat.of R M) P n).g.hom
      ((H.f n).hom f.val) = (H.f (n+1)).hom
        ((ExternalTensor.homShort k R (Y := ModuleCat.of R M) P n).g.hom f.val) at hh
    exact hh.trans ((congrArg (H.f (n+1)).hom f.property).trans (H.f (n+1)).hom.map_zero)
  let g : LinearMap.ker (ExternalTensor.homShort k R (Y := ModuleCat.of R M) P n).g.hom :=
    ⟨(H.f n).hom f.val, hg⟩
  have ht := ExternalTensor.homCochainEndExt_cycleClass k R P H n f g rfl
  rw [← nativeHomTransport_ext k R M h e he n]
  change ExternalTensor.homCochainEndExt k R P H n
    (P.extMk (ModuleCat.ofHom f.val) (n+1) rfl
      (ExternalTensor.homCycle_closed k R P n f)) = _
  refine ht.trans ?_
  exact (ResolutionProducts.map_extMk_conjugate
    (ModuleCat.restrictScalars h.toRingHom) P
    (nativeEndpointIso k R M h e he).hom (nativeEndpointIso k R M h e he).inv
    (nativeTransportResolutionHom k R M h e he)
    (ModuleCat.ofHom f.val) (ExternalTensor.homCycle_closed k R P n f)
    (ModuleCat.ofHom g.val) (ExternalTensor.homCycle_closed k R P n g)
    (by
      exact (nativeTransport_Hom k R M h e he n (ModuleCat.ofHom f.val)).trans
        (Category.assoc _ _ _).symm)).symm

end ArExplicit.ModuleBar

end

end OAI
