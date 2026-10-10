import Mathlib
import OAI.AlgebraicGeometry.RelativeTriviality.LocallyFree
import OAI.AlgebraicGeometry.RelativeTriviality.AffinePullback

namespace OAI

noncomputable section

namespace CampanaPeternellSix.RelativeCech
section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
lemma isIso_of_moduleSpecΓ_map {R : CommRingCat.{u}} {F E : (Spec R).Modules}
    [F.IsQuasicoherent] [E.IsQuasicoherent] (φ : F ⟶ E)
    [IsIso (moduleSpecΓFunctor.map φ)] : IsIso φ := by
  have hn := (tilde.adjunction (R := R)).counit.naturality φ
  simp only [Functor.id_map,Functor.comp_map] at hn
  have : IsIso (F.fromTildeΓ ≫ φ) := by
    change IsIso ((tilde.adjunction (R := R)).counit.app F ≫ φ)
    rw [← hn]
    have : IsIso ((tilde.functor R).map (moduleSpecΓFunctor.map φ)) :=
      Functor.map_isIso _ _
    have : IsIso ((tilde.adjunction (R := R)).counit.app E) :=
      inferInstanceAs (IsIso E.fromTildeΓ)
    exact IsIso.comp_isIso
  exact IsIso.of_isIso_comp_left F.fromTildeΓ φ

lemma isIso_restrict_fromSpec_of_bijective {X : Scheme.{u}} {F E : X.Modules}
    [F.IsQuasicoherent] [E.IsQuasicoherent] (φ : F ⟶ E)
    (U : X.Opens) (hU : IsAffineOpen U) (hφ : Function.Bijective (φ.app U)) :
    IsIso ((restrictFunctor hU.fromSpec).map φ) := by
  have : IsIso (moduleSpecΓFunctor.map ((restrictFunctor hU.fromSpec).map φ)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective (φ.app (hU.fromSpec ''ᵁ ⊤))
    rwa [hU.fromSpec.image_top_eq_opensRange, hU.opensRange_fromSpec]
  exact isIso_of_moduleSpecΓ_map _

lemma bijective_app_of_isIso_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {F E : Y.Modules} (φ : F ⟶ E)
    [IsIso ((restrictFunctor f).map φ)] (V : Y.Opens) (hV : V ≤ f.opensRange) :
    Function.Bijective (φ.app V) := by
  have h := (ConcreteCategory.isIso_iff_bijective (((restrictFunctor f).map φ).app (f ⁻¹ᵁ V))).mp inferInstance
  change Function.Bijective (φ.app (f ''ᵁ f ⁻¹ᵁ V)) at h
  rwa [f.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hV] at h

lemma bijective_on_subopens_of_bijective_affine {X : Scheme.{u}} {F E : X.Modules}
    [F.IsQuasicoherent] [E.IsQuasicoherent] (φ : F ⟶ E)
    (U : X.Opens) (hU : IsAffineOpen U) (hφ : Function.Bijective (φ.app U)) :
    ∀ V : X.Opens, V ≤ U → Function.Bijective (φ.app V) := by
  have := isIso_restrict_fromSpec_of_bijective φ U hU hφ
  intro V hV
  apply bijective_app_of_isIso_restrict hU.fromSpec φ V
  rwa [hU.opensRange_fromSpec]
end

section
open Module
open scoped TensorProduct
universe u v w
variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [Module.Finite R M] [Module.Flat R M]
  [Module.Finite R N] [Module.Flat R N]
lemma bijective_of_residue_bijective (f : M →ₗ[R] N)
    (hf : Function.Bijective (f.lTensor (IsLocalRing.ResidueField R))) :
    Function.Bijective f := by
  classical
  let k := IsLocalRing.ResidueField R
  have : Module.Free R M := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis R M
  have hc : Finsupp.linearCombination k (TensorProduct.mk R k N 1 ∘ (f ∘ b)) =
      (f.baseChange k).comp ((b.baseChange k).repr.symm.toLinearMap) := by
    ext index
    simp [Basis.baseChange_apply]
  have hb : Function.Bijective (Finsupp.linearCombination R (f ∘ b)) :=
    Module.IsLocalRing.linearCombination_bijective_of_flat _ (hc ▸ hf.comp (b.baseChange k).repr.symm.bijective)
  have he : f = (Finsupp.linearCombination R (f ∘ b)).comp b.repr.toLinearMap := by
    apply b.ext
    intro i
    simp
  rw [he]
  exact hb.comp b.repr.bijective
end

section
open scoped TensorProduct
open TensorProduct
universe u
variable {R M N : Type u} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [Module.Finite R M] [Module.Flat R M]
  [Module.FinitePresentation R N] [Module.Flat R N]
lemma exists_notMem_bijective_of_residue (f : M →ₗ[R] N) (p : Ideal R) [p.IsPrime]
    (hf : Function.Bijective (f.baseChange p.ResidueField)) :
    ∃ r : R, r ∉ p ∧ Function.Bijective (LocalizedModule.map (Submonoid.powers r) f) := by
  let Rp := Localization.AtPrime p
  let K := p.ResidueField
  let eM := AlgebraTensorModule.cancelBaseChange R Rp K K M
  let eN := AlgebraTensorModule.cancelBaseChange R Rp K K N
  have hc : (f.baseChange K).comp eM.toLinearMap =
      eN.toLinearMap.comp ((f.baseChange Rp).baseChange K) :=
    AlgebraTensorModule.lTensor_comp_cancelBaseChange R Rp K f
  have hk : Function.Bijective ((f.baseChange Rp).baseChange K) := by
    have hh : Function.Bijective (eN.toLinearMap.comp ((f.baseChange Rp).baseChange K)) := by
      rw [← hc]
      exact hf.comp eM.bijective
    exact (eN.comp_bijective _).mp hh
  have hp : Function.Bijective (f.baseChange Rp) := bijective_of_residue_bijective _ hk
  have hm : IsLocalizedModule.map p.primeCompl (TensorProduct.mk R Rp M 1)
      (TensorProduct.mk R Rp N 1) f = (f.baseChange Rp).restrictScalars R := by
    apply IsLocalizedModule.ext p.primeCompl (TensorProduct.mk R Rp M 1)
      (IsLocalizedModule.map_units (TensorProduct.mk R Rp N 1))
    ext m
    exact IsLocalizedModule.map_apply p.primeCompl (TensorProduct.mk R Rp M 1)
      (TensorProduct.mk R Rp N 1) f m
  apply Module.FinitePresentation.exists_notMem_bijective f p
    (TensorProduct.mk R Rp M 1) (TensorProduct.mk R Rp N 1)
  rw [hm]
  exact hp
end

section
universe u
variable {R M N M' N' : Type u} [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
  [Module R M] [Module R N] [Module R M'] [Module R N']
lemma localized_bijective_transfer (S : Submonoid R)
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    [IsLocalizedModule S f] [IsLocalizedModule S g]
    (φ : M →ₗ[R] N) (ψ : M' →ₗ[R] N')
    (hc : ψ.comp f = g.comp φ)
    (hφ : Function.Bijective (LocalizedModule.map S φ)) : Function.Bijective ψ := by
  let eM := IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S M) f
  let eN := IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S N) g
  have he : ψ.comp eM.toLinearMap = eN.toLinearMap.comp ((LocalizedModule.map S φ).restrictScalars R) := by
    apply IsLocalizedModule.ext S (LocalizedModule.mkLinearMap S M)
      (IsLocalizedModule.map_units g)
    ext x
    change ψ (eM (LocalizedModule.mkLinearMap S M x)) =
      eN (LocalizedModule.map S φ (LocalizedModule.mkLinearMap S M x))
    rw [show LocalizedModule.map S φ (LocalizedModule.mkLinearMap S M x) =
      LocalizedModule.mkLinearMap S N (φ x) from LocalizedModule.map_mk S φ x 1]
    simpa only [eM, eN, IsLocalizedModule.linearEquiv_apply, LinearMap.comp_apply] using LinearMap.congr_fun hc x
  have he' : ψ = eN.toLinearMap.comp (((LocalizedModule.map S φ).restrictScalars R).comp eM.symm.toLinearMap) := by
    ext x
    have h := LinearMap.congr_fun he (eM.symm x)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using h
  rw [he']
  exact eN.bijective.comp (hφ.comp eM.symm.bijective)
end

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
lemma affine_exists_basicOpen_bijective {R : CommRingCat.{u}} {F E : (Spec R).Modules}
    [F.IsQuasicoherent] [E.IsQuasicoherent]
    [Module.Finite R (moduleSpecΓFunctor.obj F)]
    [Module.Flat R (moduleSpecΓFunctor.obj F)]
    [Module.FinitePresentation R (moduleSpecΓFunctor.obj E)]
    [Module.Flat R (moduleSpecΓFunctor.obj E)]
    (φ : F ⟶ E) (p : PrimeSpectrum R)
    (hφ : Function.Bijective ((moduleSpecΓFunctor.map φ).hom.baseChange p.asIdeal.ResidueField)) :
    ∃ r : R, r ∉ p.asIdeal ∧ ∀ V : (Spec R).Opens,
      V ≤ PrimeSpectrum.basicOpen r → Function.Bijective (φ.app V) := by
  obtain ⟨r, hr, hbij⟩ := exists_notMem_bijective_of_residue
    (moduleSpecΓFunctor.map φ).hom p.asIdeal hφ
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen r
  let MF := modulesSpecToSheaf.obj F
  let ME := modulesSpecToSheaf.obj E
  let ρF := (MF.obj.map U.leTop.op).hom
  let ρE := (ME.obj.map U.leTop.op).hom
  have : IsLocalizedModule.Away r ρF :=
    (isIso_fromTildeΓ_iff_isLocalizing F).mp inferInstance r
  have : IsLocalizedModule.Away r ρE :=
    (isIso_fromTildeΓ_iff_isLocalizing E).mp inferInstance r
  let ψ := ((modulesSpecToSheaf.map φ).hom.app (op U)).hom
  have hc : ψ.comp ρF = ρE.comp (moduleSpecΓFunctor.map φ).hom := by
    exact congrArg ModuleCat.Hom.hom ((modulesSpecToSheaf.map φ).hom.naturality U.leTop.op)
  have hb : Function.Bijective ψ :=
    localized_bijective_transfer (Submonoid.powers r) ρF ρE _ ψ hc hbij
  refine ⟨r, hr, ?_⟩
  apply bijective_on_subopens_of_bijective_affine φ U (IsAffineOpen.Spec_basicOpen r)
  exact hb
end CampanaPeternellSix.RelativeCech

section
open CategoryTheory
universe u
lemma bijective_baseChange_of_isIso {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] {M N : ModuleCat R} (f : M ⟶ N)
    [IsIso ((ModuleCat.extendScalars (algebraMap R S)).map f)] :
    Function.Bijective (f.hom.baseChange S) := by
  have h := (ConcreteCategory.isIso_iff_bijective
    ((ModuleCat.extendScalars (algebraMap R S)).map f)).mp inferInstance
  dsimp [ModuleCat.extendScalars, ModuleCat.ExtendScalars.map',
    ConcreteCategory.hom_ofHom] at h
  let P (a : Algebra R S) : Prop := by
    letI := a
    exact Function.Bijective (f.hom.baseChange S)
  have hh : P (((algebraMap S S).comp (algebraMap R S)).toAlgebra) := h
  have ha : ((algebraMap S S).comp (algebraMap R S)).toAlgebra =
      (inferInstance : Algebra R S) := by
    rw [Algebra.algebraMap_self, RingHom.id_comp, toAlgebra_algebraMap]
  have hh' : P (inferInstance : Algebra R S) := ha ▸ hh
  exact hh'

end

namespace CampanaPeternellSix.RelativeCech
section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped TensorProduct
universe u
variable {R S : CommRingCat.{u}} (a : R ⟶ S)
lemma globalPullbackIso_naturality {F E : (Spec R).Modules}
    [F.IsQuasicoherent] [E.IsQuasicoherent] (φ : F ⟶ E) :
    (AffineBaseChange.globalPullbackIso R S a F).hom ≫
      moduleSpecΓFunctor.map ((pullback (Spec.map a)).map φ) =
    (ModuleCat.extendScalars a.hom).map (moduleSpecΓFunctor.map φ) ≫
      (AffineBaseChange.globalPullbackIso R S a E).hom := by
  apply ((ModuleCat.extendRestrictScalarsAdj a.hom).homEquiv _ _).injective
  ext m
  change moduleSpecΓFunctor.map ((pullback (Spec.map a)).map φ)
      ((AffineBaseChange.globalPullbackIso R S a F).hom
        ((ModuleCat.extendRestrictScalarsAdj a.hom).unit.app _ m)) =
    (AffineBaseChange.globalPullbackIso R S a E).hom
      ((ModuleCat.extendRestrictScalarsAdj a.hom).unit.app _ (moduleSpecΓFunctor.map φ m))
  rw [AffineBaseChange.globalPullbackIso_one, AffineBaseChange.globalPullbackIso_one]
  exact AffineBaseChange.sectionMap_naturality R S a φ m
end

section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
lemma isIso_extendScalars_map_of_isIso_pullback {R S : CommRingCat.{u}} (a : R ⟶ S)
    {F E : (Spec R).Modules} [F.IsQuasicoherent] [E.IsQuasicoherent] (φ : F ⟶ E)
    [IsIso ((pullback (Spec.map a)).map φ)] :
    IsIso ((ModuleCat.extendScalars a.hom).map (moduleSpecΓFunctor.map φ)) := by
  have : IsIso (moduleSpecΓFunctor.map ((pullback (Spec.map a)).map φ)) :=
    Functor.map_isIso _ _
  have : IsIso (((ModuleCat.extendScalars a.hom).map (moduleSpecΓFunctor.map φ)) ≫
      (AffineBaseChange.globalPullbackIso R S a E).hom) := by
    rw [← globalPullbackIso_naturality a φ]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (AffineBaseChange.globalPullbackIso R S a E).hom
lemma affine_baseChange_bijective_of_isIso_pullback {R : CommRingCat.{u}}
    (S : Type u) [CommRing S] [Algebra R S]
    {F E : (Spec R).Modules} [F.IsQuasicoherent] [E.IsQuasicoherent]
    (φ : F ⟶ E)
    [IsIso ((pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map φ)] :
    Function.Bijective ((moduleSpecΓFunctor.map φ).hom.baseChange S) := by
  have := isIso_extendScalars_map_of_isIso_pullback
    (CommRingCat.ofHom (algebraMap R S)) φ
  exact bijective_baseChange_of_isIso (moduleSpecΓFunctor.map φ)
lemma affine_residue_bijective_of_isIso_pullback {R : CommRingCat.{u}}
    {F E : (Spec R).Modules} [F.IsQuasicoherent] [E.IsQuasicoherent]
    (φ : F ⟶ E) (p : PrimeSpectrum R)
    [IsIso ((pullback (Spec.map (CommRingCat.ofHom
      (algebraMap R p.asIdeal.ResidueField)))).map φ)] :
    Function.Bijective ((moduleSpecΓFunctor.map φ).hom.baseChange p.asIdeal.ResidueField) :=
  affine_baseChange_bijective_of_isIso_pullback p.asIdeal.ResidueField φ
end

open scoped TensorProduct
open TensorProduct
universe u
variable {R K M N : Type u} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
lemma residue_bijective_of_field_bijective (f : M →ₗ[R] N)
    (p : Ideal R) [p.IsPrime] (hp : p = RingHom.ker (algebraMap R K))
    (hf : Function.Bijective (f.baseChange K)) :
    Function.Bijective (f.baseChange p.ResidueField) := by
  let k := p.ResidueField
  let a : k →+* K := Ideal.ResidueField.lift p (algebraMap R K) (le_of_eq hp) (by
    intro r hr
    change IsUnit (algebraMap R K r)
    rw [isUnit_iff_ne_zero]
    simpa [hp, RingHom.mem_ker] using hr)
  let : Algebra k K := a.toAlgebra
  have : IsScalarTower R k K := IsScalarTower.of_algebraMap_eq (fun r =>
    (Ideal.ResidueField.lift_algebraMap p (algebraMap R K) _ _ r).symm)
  let eM := AlgebraTensorModule.cancelBaseChange R k K K M
  let eN := AlgebraTensorModule.cancelBaseChange R k K K N
  have hc : (f.baseChange K).comp eM.toLinearMap =
      eN.toLinearMap.comp ((f.baseChange k).baseChange K) :=
    AlgebraTensorModule.lTensor_comp_cancelBaseChange R k K f
  have hk : Function.Bijective ((f.baseChange k).baseChange K) := by
    have hh : Function.Bijective (eN.toLinearMap.comp ((f.baseChange k).baseChange K)) := by
      rw [← hc]
      exact hf.comp eM.bijective
    exact (eN.comp_bijective _).mp hh
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective k K (f.baseChange k)).mp hk
end CampanaPeternellSix.RelativeCech

end

end OAI
