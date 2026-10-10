import OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing
import OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation

namespace OAI

namespace PiExponent.ClosedPushforwardAffine
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CoherentAffineFinite FiniteGlobalPresentation
variable {X Y : Scheme.{0}}

private def transportPresentation {Z : Scheme.{0}}
    {M N : SheafOfModules Z.ringCatSheaf} (e : M ≅ N) (P : M.Presentation) :
    N.Presentation := by
  let : IsIso e.hom := e.isIso_hom
  exact P.ofIsIso e.hom

theorem affine_pushforward_quasicoherent [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent := by
  let MX := (Scheme.Modules.pushforward X.isoSpec.hom).obj M
  have : MX.IsQuasicoherent := GlobalSectionClearing.quasicoherent_pushforward_iso X.isoSpec M
  let MY := (Scheme.Modules.pushforward (Spec.map f.appTop)).obj MX
  have : MY.IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ MY).mpr (isIso_fromTildeΓ_pushforward f.appTop MX)
  have hback : ((Scheme.Modules.pushforward Y.isoSpec.inv).obj MY).IsQuasicoherent :=
    GlobalSectionClearing.quasicoherent_pushforward_iso Y.isoSpec.symm MY
  let e₁ := (Scheme.Modules.pushforward Y.isoSpec.inv).mapIso
    ((Scheme.Modules.pushforwardComp X.isoSpec.hom (Spec.map f.appTop)).app M)
  let e₂ := (Scheme.Modules.pushforwardComp (X.isoSpec.hom ≫ Spec.map f.appTop) Y.isoSpec.inv).app M
  have hf : (X.isoSpec.hom ≫ Spec.map f.appTop) ≫ Y.isoSpec.inv = f := by
    rw [Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let e₃ := (Scheme.Modules.pushforwardCongr hf).app M
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso (e₁ ≪≫ e₂ ≪≫ e₃) hback

theorem affine_pushforward_sections_finite [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [IsClosedImmersion f] (M : X.Modules) [M.IsQuasicoherent]
    (hM : LocallyFinitelyGenerated M) :
    Module.Finite Γ(Y,⊤) Γ((Scheme.Modules.pushforward f).obj M,⊤) := by
  have hfin : Module.Finite Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) Γ(M,f ⁻¹ᵁ (⊤ : Y.Opens)) := by
    simpa only [Scheme.Hom.preimage_top] using! affine_sections_finite_of_localGenerators M hM
  let σ : Γ(Y,⊤) →+* Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) := (f.app ⊤).hom
  have : RingHomSurjective σ := ⟨f.app_surjective ⊤ (isAffineOpen_top Y)⟩
  let ψ : Γ((Scheme.Modules.pushforward f).obj M,⊤) →ₛₗ[σ] Γ(M,f ⁻¹ᵁ (⊤ : Y.Opens)) := {
    toFun := fun x => x
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  exact (ψ.finite_iff_of_bijective ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩).mpr hfin

theorem affine_exists_finitePresentation_of_sections [IsAffine X] [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] [Module.Finite Γ(X,⊤) Γ(M,⊤)] :
    ∃ P : M.Presentation, P.IsFinite := by
  let a := X.isoSpec.inv
  let b := X.isoSpec.hom
  have : IsNoetherianRing Γ(X,⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have : Module.Finite Γ(X,⊤) ((modulesSpecToSheaf.obj (M.restrict a)).obj.obj (op ⊤)) :=
    finite_isoSpec_sections M
  obtain ⟨P,hP⟩ := spec_exists_finitePresentation_of_sections (M.restrict a)
  let F : SheafOfModules (Spec Γ(X,⊤)).ringCatSheaf ⥤ SheafOfModules X.ringCatSheaf :=
    Scheme.Modules.restrictFunctor b
  let : PreservesColimitsOfSize.{0,0} F :=
    (Scheme.Modules.restrictAdjunction b).leftAdjoint_preservesColimits
  let Q := P.map F (Scheme.Modules.restrictUnitIso b).symm
  let e₁ := (Scheme.Modules.restrictFunctorComp b a).app M
  have e₂ : M.restrict (𝟙 X) ≅ ((M.restrict a).restrict b) := by
    change M.restrict (b ≫ a) ≅ ((M.restrict a).restrict b) at e₁
    simpa only [a, b, Iso.hom_inv_id] using e₁
  let e₃ := e₂.symm ≪≫ Scheme.Modules.restrictFunctorId.app M
  exact ⟨transportPresentation (Z := X) e₃ Q,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

theorem affine_pushforward_exists_finitePresentation [IsAffine X] [IsAffine Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsClosedImmersion f]
    (M : X.Modules) [M.IsQuasicoherent] (hM : LocallyFinitelyGenerated M) :
    ∃ P : ((Scheme.Modules.pushforward f).obj M).Presentation, P.IsFinite := by
  have := affine_pushforward_quasicoherent f M
  have := affine_pushforward_sections_finite f M hM
  exact affine_exists_finitePresentation_of_sections ((Scheme.Modules.pushforward f).obj M)

end
end PiExponent.ClosedPushforwardAffine

end OAI
