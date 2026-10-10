import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.AffineVanishing

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.ExtSectionComparison
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe w w' v v' u u'
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [HasExt.{w} C] [HasExt.{w'} D] {A : C} {B : D} (e : B ⟶ F.obj A)

def mapFrom (Y : C) (n : ℕ) : Ext.{w} A Y n →+ Ext.{w'} B (F.obj Y) n :=
  ((Ext.mk₀ e).precomp (F.obj Y) (zero_add n)).comp (F.mapExtAddHom A Y n)

lemma mapFrom_apply (Y : C) (n : ℕ) (x : Ext.{w} A Y n) :
    mapFrom F e Y n x = (Ext.mk₀ e).comp (x.mapExactFunctor F) (zero_add n) := rfl

@[simp] lemma mapFrom_mk₀ {Y : C} (f : A ⟶ Y) :
    mapFrom F e Y 0 (Ext.mk₀ f) = Ext.mk₀ (e ≫ F.map f) := by
  simp only [mapFrom_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

lemma mapFrom_comp {Y Z : C} {n m k : ℕ} (x : Ext.{w} A Y n)
    (y : Ext.{w} Y Z m) (h : n+m=k) :
    mapFrom F e Z k (x.comp y h) =
      (mapFrom F e Y n x).comp (y.mapExactFunctor F) h := by
  simp only [mapFrom_apply, Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc _ _ _ (zero_add _) h (by omega)).symm

theorem mapFrom_bijective [EnoughInjectives C]
    (hhom : ∀ Y : C, Function.Bijective (fun f : A ⟶ Y => e ≫ F.map f))
    (hacyclic : ∀ (I : C) [Injective I] (n : ℕ)
      (x : Ext.{w'} B (F.obj I) (n+1)), x = 0)
    (Y : C) (n : ℕ) : Function.Bijective (mapFrom F e Y n) := by
  induction n generalizing Y with
  | zero =>
    constructor
    · intro x y h
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
      obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
      rw [mapFrom_mk₀, mapFrom_mk₀] at h
      exact congrArg Ext.mk₀ ((hhom Y).injective ((Ext.mk₀_bijective _ _).injective h))
    · intro x
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
      obtain ⟨g, rfl⟩ := (hhom Y).surjective f
      exact ⟨Ext.mk₀ g, mapFrom_mk₀ F e g⟩
  | succ n ih =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    let : Injective S.X₂ := I.injective
    refine AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (mapFrom F e S.X₂ n) (mapFrom F e S.X₃ n) (mapFrom F e S.X₁ (n+1))
      ?_ ?_
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A hS n (n+1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' B (hS.map F) n (n+1) rfl))
      (ih _).surjective (ih _)
      (fun x => Ext.covariant_sequence_exact₁ A hS x (Ext.eq_zero_of_injective _) rfl)
      (fun x => Ext.covariant_sequence_exact₁ B (hS.map F) x (hacyclic S.X₂ n _) rfl)
    · ext x
      symm
      change mapFrom F e _ _ (x.comp (Ext.mk₀ S.g) (add_zero n)) =
        (mapFrom F e _ _ x).comp (Ext.mk₀ (F.map S.g)) (add_zero n)
      rw [mapFrom_comp, Ext.mapExactFunctor_mk₀]
    · ext x
      symm
      change mapFrom F e _ _ (x.comp hS.extClass rfl) =
        (mapFrom F e _ _ x).comp (hS.map F).extClass rfl
      rw [mapFrom_comp, Ext.mapExactFunctor_extClass]

end
end MaximalSeshadri.ExtSectionComparison

namespace MaximalSeshadri.RestrictionCohomology
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Abelian
open ModuleFlasque FlasqueCohomology
universe u
variable {X : Scheme.{u}} (U : X.Opens)

local instance hasExtScheme (Y : Scheme.{u}) : HasExt.{u+1} Y.Modules := HasExt.standard _

lemma freeOpenEquiv_comp {M N : X.Modules}
    (f : freeOpen X.ringCatSheaf U ⟶ M) (g : M ⟶ N) :
    freeOpenEquiv X.ringCatSheaf N U (f ≫ g) =
      g.val.app (op U) (freeOpenEquiv X.ringCatSheaf M U f) := rfl

def restrictionSectionsIso (M : X.Modules) : Γ(M.restrict U.ι,⊤) ≅ Γ(M,U) :=
  M.restrictAppIso U.ι ⊤ ≪≫ M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

def restrictionHomEquiv (M : X.Modules) :
    (freeOpen X.ringCatSheaf U ⟶ M) ≃
      (SheafOfModules.unit U.toScheme.ringCatSheaf ⟶ M.restrict U.ι) :=
  (freeOpenEquiv X.ringCatSheaf M U).trans
    ((restrictionSectionsIso U M).addCommGroupIsoToAddEquiv.toEquiv.symm.trans
      (globalHomEquiv U.toScheme.ringCatSheaf (M.restrict U.ι)).symm)

lemma restrictionHomEquiv_comp {M N : X.Modules}
    (f : freeOpen X.ringCatSheaf U ⟶ M) (g : M ⟶ N) :
    restrictionHomEquiv U N (f ≫ g) =
      restrictionHomEquiv U M f ≫ (Scheme.Modules.restrictFunctor U.ι).map g := by
  apply (globalHomEquiv U.toScheme.ringCatSheaf (N.restrict U.ι)).injective
  change (globalHomEquiv U.toScheme.ringCatSheaf (N.restrict U.ι))
      ((globalHomEquiv U.toScheme.ringCatSheaf (N.restrict U.ι)).symm
        ((restrictionSectionsIso U N).inv
          (g.val.app (op U) (freeOpenEquiv X.ringCatSheaf M U f)))) =
    (globalHomEquiv U.toScheme.ringCatSheaf (N.restrict U.ι))
      ((globalHomEquiv U.toScheme.ringCatSheaf (M.restrict U.ι)).symm
          ((restrictionSectionsIso U M).inv (freeOpenEquiv X.ringCatSheaf M U f)) ≫
        ((Scheme.Modules.restrictFunctor U.ι).map g : SheafOfModules.Hom _ _))
  erw [Equiv.apply_symm_apply, globalHomEquiv_comp, Equiv.apply_symm_apply]
  change (restrictionSectionsIso U N).inv (g.val.app (op U)
    (freeOpenEquiv X.ringCatSheaf M U f)) =
    ((Scheme.Modules.restrictFunctor U.ι).map g).val.app (op ⊤)
      ((restrictionSectionsIso U M).inv (freeOpenEquiv X.ringCatSheaf M U f))
  exact (CategoryTheory.congr_fun (g.mapPresheaf.naturality
    (eqToHom U.ι_image_top).op) _).symm

def restrictionGenerator : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
    (Scheme.Modules.restrictFunctor U.ι).obj (freeOpen X.ringCatSheaf U) :=
  restrictionHomEquiv U _ (𝟙 _)

lemma restrictionGenerator_comp {M : X.Modules}
    (f : freeOpen X.ringCatSheaf U ⟶ M) :
    restrictionGenerator U ≫ (Scheme.Modules.restrictFunctor U.ι).map f =
      restrictionHomEquiv U M f := by
  exact (restrictionHomEquiv_comp U (𝟙 _) f).symm.trans
    (congrArg (restrictionHomEquiv U M) (Category.id_comp f))

theorem restriction_ext_bijective (M : X.Modules) (n : ℕ) :
    Function.Bijective
      (ExtSectionComparison.mapFrom (Scheme.Modules.restrictFunctor U.ι)
        (restrictionGenerator U) M n) := by
  let : EnoughInjectives X.Modules :=
    ModuleGrothendieck.enoughInjectives X.ringCatSheaf
  apply ExtSectionComparison.mapFrom_bijective
  · intro N
    have heq : (fun f : freeOpen X.ringCatSheaf U ⟶ N =>
        restrictionGenerator U ≫ (Scheme.Modules.restrictFunctor U.ι).map f) =
        restrictionHomEquiv U N := funext (restrictionGenerator_comp U)
    change Function.Bijective (fun f : freeOpen X.ringCatSheaf U ⟶ N =>
      restrictionGenerator U ≫ (Scheme.Modules.restrictFunctor U.ι).map f)
    rw [heq]
    exact (restrictionHomEquiv U N).bijective
  · intro I hI n x
    let : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj I) :=
      @ModuleFlasque.injective_isFlasque _ X.ringCatSheaf I hI
    exact flasque_ext_zero U.toScheme.ringCatSheaf n (I.restrict U.ι) x

end
end MaximalSeshadri.RestrictionCohomology

namespace MaximalSeshadri.ModuleMayerVietoris
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
open ModuleFlasque
universe u w
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

def freeOpenFunctor : Opens X ⥤ SheafOfModules.{u} R :=
  yoneda ⋙ PresheafOfModules.free R.obj ⋙ PresheafOfModules.sheafification (𝟙 R.obj)

lemma freeOpen_isPushout (U V : Opens X) :
    ((Opens.mayerVietorisSquare U V).toSquare.map (freeOpenFunctor R)).IsPushout := by
  rw [Square.isPushout_iff_op_map_yoneda_isPullback]
  intro M
  have h := (Opens.mayerVietorisSquare U V).sheafCondition_of_sheaf
    ((sheafCompose (Opens.grothendieckTopology X) (forget AddCommGrpCat)).obj
      ((SheafOfModules.toSheaf R).obj M))
  apply (Square.IsPullback.iff_of_equiv _ _
    (freeOpenEquiv R M (U ⊔ V)) (freeOpenEquiv R M U)
    (freeOpenEquiv R M V) (freeOpenEquiv R M (U ⊓ V))
    ?_ ?_ ?_ ?_).mpr h
  all_goals
    ext f
    exact freeOpenEquiv_naturality R M _ f

def shortComplex (U V : Opens X) : ShortComplex (SheafOfModules.{u} R) where
  X₁ := freeOpen R (U ⊓ V)
  X₂ := freeOpen R U ⊞ freeOpen R V
  X₃ := freeOpen R (U ⊔ V)
  f := biprod.lift (freeOpenMap R (homOfLE inf_le_left))
    (-(freeOpenMap R (homOfLE inf_le_right)))
  g := biprod.desc (freeOpenMap R (homOfLE le_sup_left))
    (freeOpenMap R (homOfLE le_sup_right))
  zero := ((Opens.mayerVietorisSquare U V).toSquare.map
    (freeOpenFunctor R)).cokernelCofork.condition

instance shortComplex_mono (U V : Opens X) : Mono (shortComplex R U V).f := by
  have : Mono ((shortComplex R U V).f ≫ biprod.snd) := by
    dsimp [shortComplex]
    simp only [biprod.lift_snd]
    infer_instance
  exact mono_of_mono _ biprod.snd

lemma shortComplex_shortExact (U V : Opens X) : (shortComplex R U V).ShortExact := by
  have h := (freeOpen_isPushout R U V).isColimitCokernelCofork
  have he : (shortComplex R U V).Exact ∧ Epi (shortComplex R U V).g :=
    (shortComplex R U V).exact_and_epi_g_iff_g_is_cokernel.mpr ⟨h⟩
  let := he.2
  exact ⟨he.1⟩

variable [HasExt.{w} (SheafOfModules.{u} R)]

lemma union_ext_zero (U V : Opens X) (M : SheafOfModules.{u} R) (n : ℕ)
    (hU : ∀ x : Ext (freeOpen R U) M (n+1), x = 0)
    (hV : ∀ x : Ext (freeOpen R V) M (n+1), x = 0)
    (hUV : ∀ x : Ext (freeOpen R (U ⊓ V)) M n, x = 0)
    (x : Ext (freeOpen R (U ⊔ V)) M (n+1)) : x = 0 := by
  have hS := shortComplex_shortExact R U V
  have hmid (y : Ext (freeOpen R U ⊞ freeOpen R V) M (n+1)) : y = 0 := by
    apply Ext.biprodAddEquiv.injective
    apply Prod.ext
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_fst, Prod.fst_zero] using
        hU ((Ext.mk₀ biprod.inl).comp y (zero_add _))
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_snd, Prod.snd_zero] using
        hV ((Ext.mk₀ biprod.inr).comp y (zero_add _))
  obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₃ hS M x (hmid _) (n₀ := n) (by omega)
  have hz0 : z = 0 := hUV z
  rw [hz0, Ext.comp_zero] at hz
  exact hz.symm

end
end MaximalSeshadri.ModuleMayerVietoris


end
end
end

end OAI
