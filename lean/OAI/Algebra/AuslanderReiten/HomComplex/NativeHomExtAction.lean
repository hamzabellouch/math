import OAI.Algebra.AuslanderReiten.Ext.ExtKunnethMap
import OAI.Algebra.AuslanderReiten.HomComplex.HomCochainNativeClass
import OAI.Algebra.AuslanderReiten.Resolutions.MapResolutionExtConjugate

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (Y : Type u) [AddCommGroup Y] [Module R Y] [Module k Y] [IsScalarTower k R Y]
variable (H : homCochain k R P.complex Y ⟶ homCochain k R P.complex Y)

theorem nativeHomEndExt_extMk (n : ℕ) (f g : P.complex.X n →ₗ[R] Y)
    (hf : f.comp (P.complex.d (n+1) n).hom = 0)
    (hg : g.comp (P.complex.d (n+1) n).hom = 0)
    (hfg : (H.f n).hom f = g) :
    nativeHomEndExt k R P Y H n
      (P.extMk (ModuleCat.ofHom (X := P.complex.X n) (Y := ModuleCat.of R Y) f)
        (n+1) rfl (ModuleCat.hom_ext hf)) =
    P.extMk (ModuleCat.ofHom (X := P.complex.X n) (Y := ModuleCat.of R Y) g)
      (n+1) rfl (ModuleCat.hom_ext hg) := by
  rw [← homCochainNativeExtEquiv_literal k R P Y n f hf,
    ← homCochainNativeExtEquiv_literal k R P Y n g hg]
  change (homCochainNativeExtEquiv k R P Y n)
    ((homologyMap H n).hom ((homCochainNativeExtEquiv k R P Y n).symm
      ((homCochainNativeExtEquiv k R P Y n)
        (VectorCochain.literalClass k (homCochain k R P.complex Y) n _)))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact congrArg (homCochainNativeExtEquiv k R P Y n)
    (VectorCochain.literalClass_map k H n _ _ hfg)

theorem nativeHomEnd_closed (n : ℕ) (f : P.complex.X n →ₗ[R] Y)
    (hf : f.comp (P.complex.d (n+1) n).hom = 0) :
    (show P.complex.X n →ₗ[R] Y from (H.f n).hom f).comp
      (P.complex.d (n+1) n).hom = 0 := by
  have hh := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (H.comm n (n+1))) f
  change ((homCochain k R P.complex Y).d n (n+1)).hom ((H.f n).hom f) =
    (H.f (n+1)).hom (((homCochain k R P.complex Y).d n (n+1)).hom f) at hh
  rw [homCochain_d] at hh
  change (show P.complex.X n →ₗ[R] Y from (H.f n).hom f).comp
      (P.complex.d (n+1) n).hom =
    (H.f (n+1)).hom (f.comp (P.complex.d (n+1) n).hom) at hh
  rw [hf] at hh
  exact hh.trans (H.f (n+1)).hom.map_zero

end ArExplicit.ExternalTensor

namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (Y : Type u) [addY : AddCommGroup Y] [modY : Module R Y]
  [baseY : Module k Y] [towerY : IsScalarTower k R Y]
variable (P : ProjectiveResolution (ModuleCat.of R Y))
variable (H : homCochain k R P.complex Y ⟶ homCochain k R P.complex Y)
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive]
  [CategoryTheory.Limits.PreservesFiniteLimits F]
  [CategoryTheory.Limits.PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable (e : ModuleCat.of R Y ≅ F.obj (ModuleCat.of R Y))
variable (φ : ProjectiveResolution.Hom P (ResolutionProducts.mapResolution F P) e.hom)

theorem nativeHomEndExt_eq_exactFunctor
    (hφ : ∀ n (a : P.complex.X n ⟶ ModuleCat.of R Y),
      ModuleCat.ofHom (X := P.complex.X n) (Y := ModuleCat.of R Y) ((H.f n).hom a.hom) =
        (φ.hom.f n ≫ F.map a) ≫ e.inv)
    (n : ℕ) (x : Ext (ModuleCat.of R Y) (ModuleCat.of R Y) n) :
    nativeHomEndExt k R P Y H n x =
      ((Ext.mk₀ e.hom).comp (x.mapExactFunctor F) (zero_add n)).comp
        (Ext.mk₀ e.inv) (add_zero n) := by
  obtain ⟨a, ha, rfl⟩ := P.extMk_surjective x (n+1) rfl
  let b : P.complex.X n →ₗ[R] Y := (H.f n).hom a.hom
  have ha' : a.hom.comp (P.complex.d (n+1) n).hom = 0 :=
    congrArg ModuleCat.Hom.hom ha
  have hb := nativeHomEnd_closed k R P Y H n a.hom ha'
  have ht := nativeHomEndExt_extMk k R P Y H n a.hom b ha' hb rfl
  refine ht.trans ?_
  exact (ResolutionProducts.map_extMk_conjugate F P e.hom e.inv φ a ha
    (ModuleCat.ofHom (X := P.complex.X n) (Y := ModuleCat.of R Y) b)
    (ModuleCat.hom_ext hb) (hφ n a)).symm

end ArExplicit.ExternalTensor

end

end OAI
