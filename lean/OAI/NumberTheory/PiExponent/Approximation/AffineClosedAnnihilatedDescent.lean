import OAI.NumberTheory.PiExponent.Approximation.ClosedAnnihilatedDescent
import OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing

namespace OAI

namespace PiExponentSeshadri.ClosedAnnihilatedDescent
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
variable {R S : CommRingCat.{0}}

def surjectiveModule (φ : R ⟶ S) (hφ : Function.Surjective φ) (M : ModuleCat R)
    (h : RingHom.ker φ.hom ≤ Module.annihilator R M) : ModuleCat S :=
  (ModuleCat.restrictScalars (φ.hom.quotientKerEquivOfSurjective hφ).symm.toRingHom).obj
    (quotientModule (RingHom.ker φ.hom) M h)

def surjectiveModuleRestrictIso (φ : R ⟶ S) (hφ : Function.Surjective φ)
    (M : ModuleCat R) (h : RingHom.ker φ.hom ≤ Module.annihilator R M) :
    (ModuleCat.restrictScalars φ.hom).obj (surjectiveModule φ hφ M h) ≅ M :=
  (ModuleCat.restrictScalarsComp'App φ.hom
    (φ.hom.quotientKerEquivOfSurjective hφ).symm.toRingHom
    (Ideal.Quotient.mk (RingHom.ker φ.hom))
    (RingHom.quotientKerEquivOfSurjective_symm_comp hφ).symm
    (quotientModule (RingHom.ker φ.hom) M h)).symm ≪≫ quotientModuleRestrictIso _ M h

def specSurjectiveDescent (φ : R ⟶ S) (hφ : Function.Surjective φ)
    (M : (Spec R).Modules)
    (h : RingHom.ker φ.hom ≤ Module.annihilator R (moduleSpecΓFunctor.obj M)) :
    (Spec S).Modules := tilde (surjectiveModule φ hφ (moduleSpecΓFunctor.obj M) h)

def specSurjectiveDescentPushforwardIso (φ : R ⟶ S) (hφ : Function.Surjective φ)
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (h : RingHom.ker φ.hom ≤ Module.annihilator R (moduleSpecΓFunctor.obj M)) :
    (Scheme.Modules.pushforward (Spec.map φ)).obj (specSurjectiveDescent φ hφ M h) ≅ M :=
  specPushforwardTildeIso _ _ ≪≫
    (tilde.functor R).mapIso (surjectiveModuleRestrictIso φ hφ (moduleSpecΓFunctor.obj M) h) ≪≫
      @asIso _ _ _ _ M.fromTildeΓ
        (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M)

variable {X Y : Scheme.{0}}

def affineSpecTopSections [IsAffine X] (M : X.Modules) :
    moduleSpecΓFunctor.obj (PiExponent.GlobalSectionClearing.affineToSpecModule M) ≃ₗ[Γ(X,⊤)]
      Γ(M,⊤) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    change @SMul.smul Γ(X,⊤) Γ(M,⊤) (M.val.obj (op ⊤)).isModule.toSMul
      ((X.toSpecΓ.app ⊤)
        ((Spec Γ(X,⊤)).presheaf.map (homOfLE (show (⊤ : (Spec Γ(X,⊤)).Opens) ≤ ⊤ from le_top)).op
          ((Scheme.ΓSpecIso Γ(X,⊤)).inv r))) m =
      @SMul.smul Γ(X,⊤) Γ(M,⊤) (M.val.obj (op ⊤)).isModule.toSMul r m
    apply congrArg (fun a : Γ(X,⊤) =>
      @SMul.smul Γ(X,⊤) Γ(M,⊤) (M.val.obj (op ⊤)).isModule.toSMul a m)
    have hi : (homOfLE (show (⊤ : (Spec Γ(X,⊤)).Opens) ≤ ⊤ from le_top)).op = 𝟙 _ := rfl
    rw [hi, CategoryTheory.Functor.map_id]
    change X.toSpecΓ.appTop ((Scheme.ΓSpecIso Γ(X,⊤)).inv r) = r
    rw [Scheme.toSpecΓ_appTop]
    exact (Scheme.ΓSpecIso Γ(X,⊤)).inv_hom_id_apply r

lemma affineSpecTopSections_annihilator [IsAffine X] (M : X.Modules) (I : Ideal Γ(X,⊤))
    (h : I ≤ Module.annihilator Γ(X,⊤) Γ(M,⊤)) :
    I ≤ Module.annihilator Γ(X,⊤)
      (moduleSpecΓFunctor.obj (PiExponent.GlobalSectionClearing.affineToSpecModule M)) := by
  intro r hr
  rw [Module.mem_annihilator] at *
  intro m
  apply (affineSpecTopSections M).injective
  rw [map_smul, map_zero]
  exact Module.mem_annihilator.mp (h hr) _

def affineDescentAlong [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
    (hf : Function.Surjective f.appTop) (M : X.Modules)
    (h : RingHom.ker f.appTop.hom ≤ Module.annihilator Γ(X,⊤) Γ(M,⊤)) : Y.Modules :=
  (Scheme.Modules.pushforward Y.isoSpec.inv).obj
    (specSurjectiveDescent f.appTop hf
      (PiExponent.GlobalSectionClearing.affineToSpecModule M)
      (affineSpecTopSections_annihilator M _ h))

def affineDescentAlongPushforwardIso [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
    (hf : Function.Surjective f.appTop) (M : X.Modules) [M.IsQuasicoherent]
    (h : RingHom.ker f.appTop.hom ≤ Module.annihilator Γ(X,⊤) Γ(M,⊤)) :
    (Scheme.Modules.pushforward f).obj (affineDescentAlong f hf M h) ≅ M := by
  let A := specSurjectiveDescent f.appTop hf
    (PiExponent.GlobalSectionClearing.affineToSpecModule M)
    (affineSpecTopSections_annihilator M _ h)
  exact (Scheme.Modules.pushforwardComp Y.isoSpec.inv f).app A ≪≫
    (Scheme.Modules.pushforwardCongr (Scheme.isoSpec_inv_naturality f).symm).app A ≪≫
    ((Scheme.Modules.pushforwardComp (Spec.map f.appTop) X.isoSpec.inv).app A).symm ≪≫
    (Scheme.Modules.pushforward X.isoSpec.inv).mapIso
      (specSurjectiveDescentPushforwardIso f.appTop hf
        (PiExponent.GlobalSectionClearing.affineToSpecModule M)
        (affineSpecTopSections_annihilator M _ h)) ≪≫
    (Scheme.Modules.pushforwardComp X.isoSpec.hom X.isoSpec.inv).app M ≪≫
    (Scheme.Modules.pushforwardCongr X.isoSpec.hom_inv_id).app M ≪≫
    (Scheme.Modules.pushforwardId X).app M

theorem exists_affine_closed_descent [IsAffine X] (f : Y ⟶ X) [IsClosedImmersion f]
    (M : X.Modules) [M.IsQuasicoherent]
    (h : RingHom.ker f.appTop.hom ≤ Module.annihilator Γ(X,⊤) Γ(M,⊤)) :
    ∃ N : Y.Modules, Nonempty ((Scheme.Modules.pushforward f).obj N ≅ M) := by
  obtain ⟨hY, hf⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine f
  exact ⟨affineDescentAlong f hf M h, ⟨affineDescentAlongPushforwardIso f hf M h⟩⟩

end
end PiExponentSeshadri.ClosedAnnihilatedDescent

end OAI
