import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.SheafExactness

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.FlasqueCohomology
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Abelian
universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

def sectionsTopEquiv (M : SheafOfModules.{u} R) : M.sections ≃ M.val.obj (op ⊤) where
  toFun s := s.val (op ⊤)
  invFun t := PresheafOfModules.sectionsMk
    (fun U => M.val.map (homOfLE le_top).op t)
    (by
      intro U V i
      rw [← M.val.map_comp_apply]
      exact M.val.congr_map_apply (Subsingleton.elim _ _) t)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact s.property (homOfLE le_top).op
  right_inv t := by
    change M.val.map (𝟙 (op ⊤)) t = t
    rw [M.val.map_id]
    rfl

def globalHomEquiv (M : SheafOfModules.{u} R) :
    (SheafOfModules.unit R ⟶ M) ≃ M.val.obj (op ⊤) :=
  M.unitHomEquiv.trans (sectionsTopEquiv R M)

lemma globalHomEquiv_comp {M N : SheafOfModules.{u} R}
    (f : SheafOfModules.unit R ⟶ M) (g : M ⟶ N) :
    globalHomEquiv R N (f ≫ g) = g.val.app (op ⊤) (globalHomEquiv R M f) := rfl

theorem globalHom_surjective {S : ShortComplex (SheafOfModules.{u} R)}
    (hS : S.ShortExact)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj S.X₁)] :
    Function.Surjective (fun f : SheafOfModules.unit R ⟶ S.X₂ => f ≫ S.g) := by
  have h := ModuleSheafExact.shortExact_map R hS
  let : TopCat.Sheaf.IsFlasque ((S.map (SheafOfModules.toSheaf R)).X₁) :=
    ‹TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj S.X₁)›
  have he := TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := ⊤) h
  have hs := (AddCommGrpCat.epi_iff_surjective
    (((SheafOfModules.toSheaf R).map S.g).hom.app (op ⊤))).mp he
  intro f
  obtain ⟨t, ht⟩ := hs (globalHomEquiv R S.X₃ f)
  let t' : S.X₂.val.obj (op ⊤) := t
  have ht' : S.g.val.app (op ⊤) t' = globalHomEquiv R S.X₃ f := ht
  refine ⟨(globalHomEquiv R S.X₂).symm t', ?_⟩
  apply (globalHomEquiv R S.X₃).injective
  rw [globalHomEquiv_comp, Equiv.apply_symm_apply]
  exact ht'

instance moduleSheafHasExt : HasExt.{u+1} (SheafOfModules.{u} R) :=
  HasExt.standard _

theorem flasque_ext_zero (n : ℕ) (M : SheafOfModules.{u} R)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj M)]
    (x : Ext.{u+1} (SheafOfModules.unit R) M (n+1)) : x = 0 := by
  induction n generalizing M with
  | zero =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (SheafOfModules.unit R) hS x
      (Ext.eq_zero_of_injective _) rfl
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
    obtain ⟨g, rfl⟩ := globalHom_surjective R hS f
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
      hS.comp_extClass, Ext.comp_zero] at hy
    exact hy.symm
  | succ n ih =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    let : TopCat.Sheaf.IsFlasque ((S.map (SheafOfModules.toSheaf R)).X₁) :=
      ‹TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj M)›
    let : TopCat.Sheaf.IsFlasque ((S.map (SheafOfModules.toSheaf R)).X₂) :=
      ModuleFlasque.injective_isFlasque R (Injective.under M)
    have : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj S.X₃) :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
        (ModuleSheafExact.shortExact_map R hS)
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (SheafOfModules.unit R) hS x
      (Ext.eq_zero_of_injective _) rfl
    rw [ih S.X₃ y, Ext.zero_comp] at hy
    exact hy.symm

end
end MaximalSeshadri.FlasqueCohomology

namespace MaximalSeshadri.AffineCohomology
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Abelian
open FlasqueCohomology
universe u
variable {R : CommRingCat.{u}}

def structureSheafUnit (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

def schemeGlobalHomEquiv (X : Scheme.{u}) (M : X.Modules) :
    (structureSheafUnit X ⟶ M) ≃ (Scheme.Modules.presheaf M).obj (op ⊤) :=
  globalHomEquiv X.ringCatSheaf M

lemma globalHom_tilde_surjective {M N : ModuleCat.{u} R} (g : M ⟶ N) [Epi g] :
    Function.Surjective (fun f : structureSheafUnit (Spec R) ⟶ tilde M =>
      f ≫ tilde.map g) := by
  intro f
  obtain ⟨q,hq⟩ := (ConcreteCategory.bijective_of_isIso (tilde.toOpen N ⊤)).surjective
    (schemeGlobalHomEquiv (Spec R) (tilde N) f)
  obtain ⟨p,hp⟩ := (ModuleCat.epi_iff_surjective g).mp inferInstance q
  let lifted : (Scheme.Modules.presheaf (tilde M)).obj (op ⊤) := tilde.toOpen M ⊤ p
  refine ⟨(schemeGlobalHomEquiv (Spec R) (tilde M)).symm lifted, ?_⟩
  apply (schemeGlobalHomEquiv (Spec R) (tilde N)).injective
  change ((tilde.map g).app ⊤)
    ((schemeGlobalHomEquiv (Spec R) (tilde M))
      ((schemeGlobalHomEquiv (Spec R) (tilde M)).symm lifted)) = _
  rw [Equiv.apply_symm_apply]
  change ((modulesSpecToSheaf.map (tilde.map g)).hom.app (op ⊤)) (tilde.toOpen M ⊤ p) = _
  have h := CategoryTheory.congr_fun (tilde.toOpen_map_app g ⊤) p
  exact h.trans (by change tilde.toOpen N ⊤ (g p) = _; rw [hp, hq])

local instance affineHasExt : HasExt.{u+1} (Spec R).Modules := HasExt.standard _

theorem tilde_ext_zero [IsNoetherianRing R] (n : ℕ) (M : ModuleCat.{u} R)
    (x : Ext.{u+1} (C := (Spec R).Modules)
      (structureSheafUnit (Spec R)) (tilde M) (n+1)) : x = 0 := by
  induction n generalizing M with
  | zero =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    let T : ShortComplex (Spec R).Modules :=
      { X₁ := tilde S.X₁
        X₂ := tilde S.X₂
        X₃ := tilde S.X₃
        f := tilde.map S.f
        g := tilde.map S.g
        zero := (S.map (tilde.functor R)).zero }
    have hT : T.ShortExact := hS.map (tilde.functor R)
    let : Injective S.X₂ := (inferInstance : Injective (Injective.under M))
    let : Module.Injective R S.X₂ := Module.injective_module_of_injective_object R S.X₂
    obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₁ _ hT x
      (flasque_ext_zero (Spec R).ringCatSheaf 0 (tilde S.X₂) _) rfl
    obtain ⟨f,rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
    obtain ⟨g,rfl⟩ := globalHom_tilde_surjective S.g f
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
      show (Ext.mk₀ (tilde.map S.g)).comp hT.extClass rfl = 0 from hT.comp_extClass,
      Ext.comp_zero] at hy
    exact hy.symm
  | succ n ih =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    let T : ShortComplex (Spec R).Modules :=
      { X₁ := tilde S.X₁
        X₂ := tilde S.X₂
        X₃ := tilde S.X₃
        f := tilde.map S.f
        g := tilde.map S.g
        zero := (S.map (tilde.functor R)).zero }
    have hT : T.ShortExact := hS.map (tilde.functor R)
    let : Injective S.X₂ := (inferInstance : Injective (Injective.under M))
    let : Module.Injective R S.X₂ := Module.injective_module_of_injective_object R S.X₂
    obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₁ _ hT x
      (flasque_ext_zero (Spec R).ringCatSheaf (n+1) (tilde S.X₂) _) rfl
    rw [ih S.X₃ y, Ext.zero_comp] at hy
    exact hy.symm

theorem quasicoherent_ext_zero [IsNoetherianRing R] (n : ℕ) (M : (Spec R).Modules)
    [M.IsQuasicoherent]
    (x : Ext.{u+1} (C := (Spec R).Modules)
      (structureSheafUnit (Spec R)) M (n+1)) : x = 0 := by
  let e := asIso M.fromTildeΓ
  have hx := tilde_ext_zero n _ (x.comp (Ext.mk₀ e.inv) (add_zero _))
  have h := congrArg (fun y => y.comp (Ext.mk₀ e.hom) (add_zero (n+1))) hx
  simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    e.inv_hom_id, Ext.comp_mk₀_id, Ext.zero_comp] using h

end
end MaximalSeshadri.AffineCohomology

namespace MaximalSeshadri.RestrictionExact
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

instance restriction_mono {M N : Y.Modules} (g : M ⟶ N) [Mono g] :
    Mono ((Scheme.Modules.restrictFunctor f).map g) := by
  apply (Scheme.Modules.toPresheafOfModules X).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U
  let : Mono g.val := inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules Y).map g))
  exact PresheafOfModules.injective_of_mono g.val (op (f ''ᵁ U.unop))

instance restriction_preservesMonomorphisms :
    (Scheme.Modules.restrictFunctor f).PreservesMonomorphisms where
  preserves g _ := restriction_mono f g

instance restriction_additive : (Scheme.Modules.restrictFunctor f).Additive where
  map_add := by intros; ext; rfl

instance restriction_preservesHomology :
    (Scheme.Modules.restrictFunctor f).PreservesHomology :=
  (Scheme.Modules.restrictFunctor f).preservesHomology_of_preservesMonos_and_cokernels

instance restriction_preservesFiniteLimits :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) :=
  (Scheme.Modules.restrictFunctor f).preservesFiniteLimits_of_preservesHomology

instance restriction_flasque (M : Y.Modules)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M)] :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj (M.restrict f)) where
  epi {U V} i := by
    change Epi (((SheafOfModules.toSheaf Y.ringCatSheaf).obj M).obj.map
      (f.opensFunctor.map i.unop).op)
    exact TopCat.Presheaf.IsFlasque.epi _

end
end MaximalSeshadri.RestrictionExact

namespace MaximalSeshadri.AffineSchemeCohomology
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian
open Scheme.Modules
universe u

def restrictionEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) : Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (restrictFunctor e.hom) (restrictFunctor e.inv)
    ((restrictFunctorId (X := Y)).symm ≪≫ (restrictFunctorCongr e.inv_hom_id).symm ≪≫
      restrictFunctorComp e.inv e.hom)
    ((restrictFunctorComp e.hom e.inv).symm ≪≫ restrictFunctorCongr e.hom_inv_id ≪≫
      restrictFunctorId (X := X))

local instance hasExtScheme (X : Scheme.{u}) : HasExt.{u+1} X.Modules := HasExt.standard _

theorem affine_ext_zero (X : Scheme.{u}) [IsAffine X] [IsNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (x : Ext.{u+1} (C := X.Modules)
      (AffineCohomology.structureSheafUnit X) M (n+1)) : x = 0 := by
  let : IsNoetherianRing Γ(X, ⊤) := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  let E := restrictionEquivalence X.isoSpec.symm
  let F := E.functor
  let : F.Additive := RestrictionExact.restriction_additive _
  let : EnoughInjectives X.Modules := ModuleGrothendieck.enoughInjectives X.ringCatSheaf
  let e : F.obj (AffineCohomology.structureSheafUnit X) ≅
      AffineCohomology.structureSheafUnit (Spec Γ(X, ⊤)) :=
    restrictUnitIso X.isoSpec.inv
  let z : Ext.{u+1} (F.obj (AffineCohomology.structureSheafUnit X)) (F.obj M) (n+1) :=
    x.mapExactFunctor F
  have hz : z = 0 := by
    have hw : (Ext.mk₀ e.inv).comp z (zero_add _) = 0 :=
      AffineCohomology.quasicoherent_ext_zero n (M.restrict X.isoSpec.inv)
        ((Ext.mk₀ e.inv).comp z (zero_add _))
    have h := congrArg (fun y => (Ext.mk₀ e.hom).comp y (zero_add (n+1))) hw
    simpa only [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp,
      Ext.comp_zero] using h
  have hb : Function.Injective (F.mapExtAddHom (AffineCohomology.structureSheafUnit X) M (n+1) :
      Ext.{u+1} (C := X.Modules) (AffineCohomology.structureSheafUnit X) M (n+1) →
      Ext.{u+1} (F.obj (AffineCohomology.structureSheafUnit X)) (F.obj M) (n+1)) :=
    (F.mapExt_bijective_of_preservesInjectiveObjects _ _ (n+1)).injective
  apply hb
  simpa only [Functor.mapExtAddHom_apply, Ext.mapExactFunctor_zero] using hz

end
end MaximalSeshadri.AffineSchemeCohomology


end
end
end

end OAI
