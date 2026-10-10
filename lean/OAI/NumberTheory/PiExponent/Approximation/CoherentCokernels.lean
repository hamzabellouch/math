import OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation

namespace OAI

namespace PiExponent.CoherentCokernels
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponent.FiniteGlobalPresentation PiExponent.CoherentAffineFinite
universe u

private def presentationOfIso (X : Scheme.{u})
    {M N : SheafOfModules.{u} X.ringCatSheaf} (e : M ≅ N)
    (P : M.Presentation) : N.Presentation := by
  let : IsIso e.hom := e.isIso_hom
  exact P.ofIsIso e.hom

def specCokernelIso {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    let g := (tilde.functor R).preimage
      ((asIso M.fromTildeΓ).hom ≫ f ≫ (asIso N.fromTildeΓ).inv)
    (tilde.functor R).obj (cokernel g) ≅ cokernel f := by
  intro g
  let hm := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let hn := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  let em := @asIso _ _ _ _ M.fromTildeΓ hm
  let en := @asIso _ _ _ _ N.fromTildeΓ hn
  exact PreservesCokernel.iso (tilde.functor R) g ≪≫
    cokernel.mapIso ((tilde.functor R).map g) f em en (by
        change (tilde.functor R).map ((tilde.functor R).preimage _) ≫ _ = _
        erw [Functor.map_preimage]
        exact (Category.assoc em.hom (f ≫ en.inv) en.hom).trans
          (congrArg (fun q => em.hom ≫ q)
            ((Category.assoc f en.inv en.hom).trans
              ((congrArg (fun q => f ≫ q) en.inv_hom_id).trans (Category.comp_id f)))))

theorem spec_cokernel_exists_finitePresentation {R : CommRingCat.{u}} [IsNoetherianRing R]
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    [Module.Finite R ((modulesSpecToSheaf.obj N).obj.obj (op ⊤))] (f : M ⟶ N) :
    ∃ P : (cokernel f).Presentation, P.IsFinite := by
  let g := (tilde.functor R).preimage
    ((asIso M.fromTildeΓ).hom ≫ f ≫ (asIso N.fromTildeΓ).inv)
  have : Module.Finite R (moduleSpecΓFunctor.obj N) := inferInstanceAs
    (Module.Finite R ((modulesSpecToSheaf.obj N).obj.obj (op ⊤)))
  have : Module.Finite R (cokernel (C := ModuleCat R) g) :=
    Module.Finite.of_surjective (cokernel.π g).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  obtain ⟨P,hP⟩ := tilde_exists_finitePresentation (cokernel g)
  exact ⟨presentationOfIso (Spec R) (specCokernelIso f) P,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

theorem affine_cokernel_exists_finitePresentation {X : Scheme.{u}}
    [IsAffine X] [IsLocallyNoetherian X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    (hN : LocallyFinitelyGenerated N) :
    ∃ P : (cokernel f).Presentation, P.IsFinite := by
  let a := X.isoSpec.inv
  let F := Scheme.Modules.restrictFunctor a
  have : IsNoetherianRing Γ(X,⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have : Module.Finite Γ(X,⊤) ((modulesSpecToSheaf.obj (N.restrict a)).obj.obj (op ⊤)) :=
    spec_sections_finite_of_localGenerators (N.restrict a) (hN.restrict a)
  obtain ⟨P,hP⟩ := spec_cokernel_exists_finitePresentation (F.map f)
  let e := PreservesCokernel.iso F f
  let P' := presentationOfIso (Spec Γ(X,⊤)) e.symm P
  let b := X.isoSpec.hom
  let G : SheafOfModules (Spec Γ(X,⊤)).ringCatSheaf ⥤ SheafOfModules X.ringCatSheaf :=
    Scheme.Modules.restrictFunctor b
  let : PreservesColimitsOfSize.{u,u} G :=
    (Scheme.Modules.restrictAdjunction b).leftAdjoint_preservesColimits
  let Q := P'.map G (Scheme.Modules.restrictUnitIso b).symm
  let e₁ := (Scheme.Modules.restrictFunctorComp b a).app (cokernel f)
  have e₂ : (cokernel f).restrict (𝟙 X) ≅ ((cokernel f).restrict a).restrict b := by
    change (cokernel f).restrict (b ≫ a) ≅ ((cokernel f).restrict a).restrict b at e₁
    simpa only [b, a, Iso.hom_inv_id] using e₁
  let e₃ := e₂.symm ≪≫ Scheme.Modules.restrictFunctorId.app (cokernel f)
  exact ⟨presentationOfIso X e₃ Q,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

theorem cokernel_isFinitePresentation {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsFinitePresentation] (f : M ⟶ N) :
    (cokernel f).IsFinitePresentation := by
  apply isFinitePresentation_of_affine_presentations
  intro U
  have : IsAffine U.1.toScheme := U.2
  let F := Scheme.Modules.restrictFunctor U.1.ι
  let : N.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData N).choose.isQuasicoherent
  obtain ⟨P,hP⟩ := affine_cokernel_exists_finitePresentation (F.map f)
    ((locallyFinitelyGenerated_of_finitePresentation N).restrict U.1.ι)
  let e := PreservesCokernel.iso F f
  exact ⟨presentationOfIso U.1.toScheme e.symm P,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩
end
end PiExponent.CoherentCokernels

end OAI
