import Mathlib

namespace OAI

namespace PiExponent.CoherentAffineFinite
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

private theorem epi_iso_comp_iso {C : Type*} [Category C] {A B D E : C}
    (i : A ≅ B) (p : B ⟶ D) (hp : Epi p) (j : D ≅ E) :
    Epi (i.hom ≫ p ≫ j.hom) := by
  let : Epi p := hp
  infer_instance

private theorem finitePresentation_quasicoherent {X : Scheme.{u}}
    (M : X.Modules) [M.IsFinitePresentation] : M.IsQuasicoherent :=
  (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent

theorem spec_sections_finite_of_generators {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (s : M.GeneratingSections) [hs : s.IsFiniteType] :
    Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤)) := by
  let : Finite s.I := hs.finite
  let : Fintype s.I := Fintype.ofFinite s.I
  let N : ModuleCat R := (modulesSpecToSheaf.obj M).obj.obj (op ⊤)
  let a : tilde (ModuleCat.of R (s.I →₀ R)) ⟶ tilde N :=
    (tildeFinsupp s.I).hom ≫ s.π ≫ (asIso M.fromTildeΓ).inv
  let f : ModuleCat.of R (s.I →₀ R) ⟶ N := (tilde.functor R).preimage a
  have : Epi s.π := s.epi
  have : Epi (asIso M.fromTildeΓ).inv := inferInstance
  have ha : Epi a := by
    change Epi ((tildeFinsupp s.I).hom ≫ s.π ≫ (asIso M.fromTildeΓ).inv)
    exact epi_iso_comp_iso (tildeFinsupp s.I) s.π s.epi (asIso M.fromTildeΓ).symm
  have hf : Epi f := (tilde.functor R).epi_of_epi_map (by
    change Epi ((tilde.functor R).map ((tilde.functor R).preimage a))
    exact (Functor.map_preimage (tilde.functor R) a).symm ▸ ha)
  exact Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective f).mp hf)

theorem affine_sections_finite_of_generators {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent]
    (s : M.GeneratingSections) [hs : s.IsFiniteType] : Module.Finite Γ(X,⊤) Γ(M,⊤) := by
  let f := X.isoSpec.inv
  let F : SheafOfModules X.ringCatSheaf ⥤ SheafOfModules (Spec Γ(X,⊤)).ringCatSheaf :=
    Scheme.Modules.restrictFunctor f
  let : Limits.PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.restrictAdjunction f).leftAdjoint_preservesColimits
  let J := M.restrict f
  let t := s.map F (Scheme.Modules.restrictUnitIso f).symm
  let : t.IsFiniteType := ⟨hs.finite⟩
  let R := Γ(X,⊤)
  let N := (modulesSpecToSheaf.obj J).obj.obj (op ⊤)
  let : Module.Finite R N := spec_sections_finite_of_generators J t
  let σ : R →+* Γ(X,f ''ᵁ ⊤) := (f.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let φ : N →ₛₗ[σ] Γ(M,f ''ᵁ ⊤) := {
    toFun := (M.restrictAppIso f ⊤).hom
    map_add' := map_add _
    map_smul' := by intro r m; rfl }
  have hφ : Function.Surjective φ :=
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso f ⊤).hom).surjective
  have hf : f ''ᵁ (⊤ : (Spec R).Opens) = ⊤ := by
    ext x
    change (∃ y : Spec R, y ∈ (⊤ : (Spec R).Opens) ∧ f y = x) ↔ True
    simp only [Opens.mem_top, true_and, iff_true]
    exact (ConcreteCategory.bijective_of_isIso f.base).surjective x
  have h := Module.Finite.of_surjective φ hφ
  rw [hf] at h
  exact h

def LocallyFinitelyGenerated {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    ∃ s : (M.restrict U.ι).GeneratingSections, s.IsFiniteType

theorem locallyFinitelyGenerated_of_finitePresentation {X : Scheme.{u}}
    (M : X.Modules) [M.IsFinitePresentation] : LocallyFinitelyGenerated M := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  intro x
  have hcov := q.coversTop
  rw [Opens.coversTop_iff] at hcov
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, q.X i by rw [hcov]; trivial)
  refine ⟨q.X i, hi, ?_⟩
  let F : SheafOfModules (Sheaf.over X.ringCatSheaf (q.X i)) ⥤
      SheafOfModules (Scheme.Opens.toScheme (X := X) (q.X i)).ringCatSheaf :=
    (Scheme.Modules.overEquiv (q.X i)).functor
  let : Limits.PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.overEquiv (q.X i)).toAdjunction.leftAdjoint_preservesColimits
  let t := (q.presentation i).generators.map F (Iso.refl _)
  let e := (Scheme.Modules.overFunctorEquiv (q.X i)).app M
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso e t,
    ⟨(hq.isFinite_presentation i).isFiniteType_generators.finite⟩⟩

theorem finite_generators_of_le {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (s : (M.restrict U.ι).GeneratingSections) [s.IsFiniteType] :
    ∃ t : (M.restrict V.ι).GeneratingSections, t.IsFiniteType := by
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤ SheafOfModules V.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor (X.homOfLE h)
  let : Limits.PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.restrictAdjunction (X.homOfLE h)).leftAdjoint_preservesColimits
  let t := s.map F
    (Scheme.Modules.restrictUnitIso (X.homOfLE h)).symm
  let e := (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M
  simp only [X.homOfLE_ι h] at e
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso e.symm t,
    ⟨SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := s)⟩⟩

theorem affine_open_sections_finite_of_generators {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U)
    (s : (M.restrict U.ι).GeneratingSections) [s.IsFiniteType] :
    Module.Finite Γ(X,U) Γ(M,U) := by
  let : IsAffine U.toScheme := hU
  let : Module.Finite Γ(U.toScheme,⊤) Γ(M.restrict U.ι,⊤) :=
    affine_sections_finite_of_generators (M.restrict U.ι) s
  let σ := (U.ι.appIso ⊤).inv.hom
  let φ : Γ(M.restrict U.ι,⊤) →ₛₗ[σ] Γ(M,U.ι ''ᵁ ⊤) := {
    toFun := (M.restrictAppIso U.ι ⊤).hom
    map_add' := map_add _
    map_smul' := by intro r m; rfl }
  have hφ : Function.Surjective φ :=
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso U.ι ⊤).hom).surjective
  have h := Module.Finite.of_surjective φ hφ
  rwa [U.ι_image_top] at h

theorem spec_sections_finite_of_localGenerators {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] (hM : LocallyFinitelyGenerated M) :
    Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤)) := by
  classical
  let D (r : R) : (Spec R).Opens := PrimeSpectrum.basicOpen r
  let t : Set R := {r | ∃ s : (M.restrict (D r).ι).GeneratingSections, s.IsFiniteType}
  have ht : Ideal.span t = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff']
    apply top_unique
    intro x hx
    obtain ⟨U,hxU,s,hs⟩ := hM x
    obtain ⟨_,⟨_,⟨r,rfl⟩,rfl⟩,hxr,hrU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.isOpen
    exact Opens.mem_iSup.mpr ⟨r, Opens.mem_iSup.mpr
      ⟨finite_generators_of_le M hrU s,hxr⟩⟩
  let N := (modulesSpecToSheaf.obj M).obj.obj (op ⊤)
  let A (r : t) := Γ(Spec R, PrimeSpectrum.basicOpen r.val)
  let P (r : t) := Γ(M, PrimeSpectrum.basicOpen r.val)
  let (r : t) : Algebra R (A r) := StructureSheaf.openAlgebra (R := R) (op (PrimeSpectrum.basicOpen r.val))
  let (r : t) : IsLocalization.Away r.val (A r) := inferInstanceAs
    (IsLocalization.Away r.val ((Spec.structureSheaf R).obj.obj (op (PrimeSpectrum.basicOpen r.val))))
  let (r : t) : Module (A r) (P r) :=
    (M.val.obj (op (PrimeSpectrum.basicOpen r.val))).isModule
  let (r : t) : Module R (P r) :=
    ((modulesSpecToSheaf.obj M).obj.obj (op (PrimeSpectrum.basicOpen r.val))).isModule
  let (r : t) : IsScalarTower R (A r) (P r) :=
    IsScalarTower.of_compHom R (A r) (P r)
  let f (r : t) : N →ₗ[R] P r :=
    ((modulesSpecToSheaf.obj M).obj.map (homOfLE le_top).op).hom
  have hloc := (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance
  let (r : t) : IsLocalizedModule.Away r.val (f r) := hloc r.val
  have hfin (r : t) : Module.Finite (A r) (P r) := by
    obtain ⟨s, hs⟩ := r.property
    exact affine_open_sections_finite_of_generators M (D r.val)
      (IsAffineOpen.Spec_basicOpen r.val) s
  exact Module.Finite.of_localizationSpan' t ht f hfin

theorem LocallyFinitelyGenerated.restrict {X Y : Scheme.{u}} {M : Y.Modules}
    (hM : LocallyFinitelyGenerated M) (f : X ⟶ Y) [IsOpenImmersion f] :
    LocallyFinitelyGenerated (M.restrict f) := by
  intro x
  obtain ⟨U, hxU, s, hs⟩ := hM (f x)
  let V := f ⁻¹ᵁ U
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤ SheafOfModules V.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor (f ∣_ U)
  let : Limits.PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.restrictAdjunction (f ∣_ U)).leftAdjoint_preservesColimits
  let t := s.map F
    (Scheme.Modules.restrictUnitIso (f ∣_ U)).symm
  let e := (Scheme.Modules.restrictFunctorComp (f ∣_ U) U.ι).app M
  have e' : M.restrict (V.ι ≫ f) ≅ (M.restrict U.ι).restrict (f ∣_ U) := by
    change M.restrict ((f ∣_ U) ≫ U.ι) ≅ (M.restrict U.ι).restrict (f ∣_ U) at e
    simpa only [V, morphismRestrict_ι] using e
  let e'' := ((Scheme.Modules.restrictFunctorComp V.ι f).app M).symm ≪≫ e'
  exact ⟨V, hxU, SheafOfModules.GeneratingSections.equivOfIso e''.symm t,
    ⟨SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := s)⟩⟩

theorem affine_sections_finite_of_localGenerators {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] (hM : LocallyFinitelyGenerated M) :
    Module.Finite Γ(X,⊤) Γ(M,⊤) := by
  let f := X.isoSpec.inv
  let J := M.restrict f
  let R := Γ(X,⊤)
  let N := (modulesSpecToSheaf.obj J).obj.obj (op ⊤)
  let : Module.Finite R N := spec_sections_finite_of_localGenerators J
    (hM.restrict f)
  let σ : R →+* Γ(X,f ''ᵁ ⊤) := (f.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let φ : N →ₛₗ[σ] Γ(M,f ''ᵁ ⊤) := {
    toFun := (M.restrictAppIso f ⊤).hom
    map_add' := map_add _
    map_smul' := by intro r m; rfl }
  have hφ : Function.Surjective φ :=
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso f ⊤).hom).surjective
  have hf : f ''ᵁ (⊤ : (Spec R).Opens) = ⊤ := by
    ext x
    change (∃ y : Spec R, y ∈ (⊤ : (Spec R).Opens) ∧ f y = x) ↔ True
    simp only [Opens.mem_top, true_and, iff_true]
    exact (ConcreteCategory.bijective_of_isIso f.base).surjective x
  have h := Module.Finite.of_surjective φ hφ
  rw [hf] at h
  exact h

theorem affine_sections_finite {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsFinitePresentation] : Module.Finite Γ(X,⊤) Γ(M,⊤) := by
  let := finitePresentation_quasicoherent M
  exact affine_sections_finite_of_localGenerators M (locallyFinitelyGenerated_of_finitePresentation M)

theorem finite_isoSpec_sections {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [Module.Finite Γ(X,⊤) Γ(M,⊤)] :
    Module.Finite Γ(X,⊤)
      ((modulesSpecToSheaf.obj (M.restrict X.isoSpec.inv)).obj.obj (op ⊤)) := by
  let f := X.isoSpec.inv
  let R := Γ(X,⊤)
  let N : ModuleCat R := (modulesSpecToSheaf.obj (M.restrict f)).obj.obj (op ⊤)
  have hf : f ''ᵁ (⊤ : (Spec R).Opens) = ⊤ := by
    ext x
    change (∃ y : Spec R, y ∈ (⊤ : (Spec R).Opens) ∧ f y = x) ↔ True
    simp only [Opens.mem_top, true_and, iff_true]
    exact (ConcreteCategory.bijective_of_isIso f.base).surjective x
  have : Module.Finite Γ(X,f ''ᵁ ⊤) Γ(M,f ''ᵁ ⊤) := by
    rw [hf]
    infer_instance
  let σ : Γ(X,f ''ᵁ ⊤) →+* R := (Scheme.ΓSpecIso R).hom.hom.comp (f.appIso ⊤).hom.hom
  let φ : Γ(M,f ''ᵁ ⊤) →ₛₗ[σ] N := {
    toFun := (M.restrictAppIso f ⊤).inv
    map_add' := map_add _
    map_smul' := by
      intro r m
      change (M.restrictAppIso f ⊤).inv (r • m) =
        ((Scheme.ΓSpecIso R).inv ((Scheme.ΓSpecIso R).hom ((f.appIso ⊤).hom r))) •
          (M.restrictAppIso f ⊤).inv m
      rw [Iso.hom_inv_id_apply]
      exact congr($(M.smul_restrictAppIso_inv f ⊤ r) m) }
  exact Module.Finite.of_surjective φ
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso f ⊤).inv).surjective

theorem spec_exists_finite_generators {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤))] :
    ∃ s : M.GeneratingSections, s.IsFiniteType := by
  let N : ModuleCat R := (modulesSpecToSheaf.obj M).obj.obj (op ⊤)
  obtain ⟨I,hI,v,hv⟩ : ∃ (I : Type u) (_ : Finite I) (v : I → N),
      Submodule.span R (Set.range v) = ⊤ :=
    Submodule.fg_iff_exists_finite_generating_family.mp (Module.Finite.fg_top (R := R) (M := N))
  let f : ModuleCat.of R (I →₀ R) ⟶ N := ModuleCat.ofHom (X := I →₀ R) (Y := N) (Finsupp.linearCombination (M := N) R v)
  have : Epi f := (ModuleCat.epi_iff_surjective f).mpr <| by
    change Function.Surjective (Finsupp.linearCombination (M := N) R v)
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hv]
  let p : SheafOfModules.free I ⟶ M :=
    (tildeFinsupp I).inv ≫ (tilde.functor R).map f ≫ M.fromTildeΓ
  have hmap : Epi ((tilde.functor R).map f) := inferInstance
  have : Epi M.fromTildeΓ := inferInstance
  have hp : Epi p := by
    change Epi ((tildeFinsupp I).inv ≫ (tilde.functor R).map f ≫ M.fromTildeΓ)
    let hΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
    exact epi_iso_comp_iso (tildeFinsupp I).symm ((tilde.functor R).map f) hmap
      (@asIso _ _ _ _ M.fromTildeΓ hΓ)
  let s : M.GeneratingSections := {
    I := I
    s := M.freeHomEquiv p
    epi := by simpa only [Equiv.symm_apply_apply] using hp }
  exact ⟨s, ⟨hI⟩⟩

theorem affine_exists_finite_generators {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] [Module.Finite Γ(X,⊤) Γ(M,⊤)] :
    ∃ s : M.GeneratingSections, s.IsFiniteType := by
  let f := X.isoSpec.inv
  let J := M.restrict f
  let : Module.Finite Γ(X,⊤) ((modulesSpecToSheaf.obj J).obj.obj (op ⊤)) :=
    finite_isoSpec_sections M
  obtain ⟨s,hs⟩ := spec_exists_finite_generators J
  let g := X.isoSpec.hom
  let F : SheafOfModules (Spec Γ(X,⊤)).ringCatSheaf ⥤ SheafOfModules X.ringCatSheaf :=
    Scheme.Modules.restrictFunctor g
  let : Limits.PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.restrictAdjunction g).leftAdjoint_preservesColimits
  let t := s.map F (Scheme.Modules.restrictUnitIso g).symm
  let e₁ := (Scheme.Modules.restrictFunctorComp g f).app M
  have e₂ : M.restrict (𝟙 X) ≅ J.restrict g := by
    change M.restrict (g ≫ f) ≅ J.restrict g at e₁
    simpa only [g, f, Iso.hom_inv_id] using e₁
  let e := e₂.symm ≪≫ Scheme.Modules.restrictFunctorId.app M
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso e t,
    ⟨hs.finite⟩⟩

theorem affine_exists_finite_generators_of_finitePresentation {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsFinitePresentation] :
    ∃ s : M.GeneratingSections, s.IsFiniteType := by
  let := finitePresentation_quasicoherent M
  have := affine_sections_finite M
  exact affine_exists_finite_generators M

theorem affine_open_sections_finite {X : Scheme.{u}} (M : X.Modules)
    [M.IsFinitePresentation] (U : X.Opens) (hU : IsAffineOpen U) :
    Module.Finite Γ(X,U) Γ(M,U) := by
  let : IsAffine U.toScheme := hU
  let := finitePresentation_quasicoherent M
  have := affine_sections_finite_of_localGenerators (M.restrict U.ι)
    ((locallyFinitelyGenerated_of_finitePresentation M).restrict U.ι)
  obtain ⟨s,hs⟩ := affine_exists_finite_generators (M.restrict U.ι)
  exact affine_open_sections_finite_of_generators M U hU s

end
end PiExponent.CoherentAffineFinite

end OAI
