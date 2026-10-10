import Mathlib

namespace OAI

namespace PiExponent.GlobalSectionClearing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}}

def restrictScalar (X : Scheme.{u}) (U : X.Opens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom

lemma restrictScalar_naturality (X : Scheme.{u}) {U V : X.Opens} (i : U ⟶ V) (r : Γ(X, ⊤)) :
    X.presheaf.map i.op (restrictScalar X V r) = restrictScalar X U r := by
  change (X.presheaf.map (homOfLE le_top).op ≫ X.presheaf.map i.op) r = _
  rw [← X.presheaf.map_comp]
  rfl

def OpenSections (M : X.Modules) (U : X.Opens) := Γ(M,U)
instance (M : X.Modules) (U : X.Opens) : AddCommGroup (OpenSections M U) :=
  inferInstanceAs (AddCommGroup Γ(M,U))
instance (M : X.Modules) (U : X.Opens) : Module Γ(X,⊤) (OpenSections M U) :=
  Module.compHom Γ(M,U) (restrictScalar X U)

def openRestriction (M : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    OpenSections M V →ₗ[Γ(X,⊤)] OpenSections M U where
  toFun := M.val.map (homOfLE h).op
  map_add' := map_add _
  map_smul' := by
    intro r m
    let : Module Γ(X,V) (OpenSections M V) := (M.val.obj (op V)).isModule
    let : Module Γ(X,U) (OpenSections M U) := (M.val.obj (op U)).isModule
    change M.presheaf.map (homOfLE h).op (restrictScalar X V r • (m : Γ(M,V))) =
      restrictScalar X U r • M.presheaf.map (homOfLE h).op m
    erw [M.map_smul, restrictScalar_naturality]

theorem quasicoherent_pushforward_iso (e : X ≅ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward e.hom).obj M).IsQuasicoherent := by
  let N := (Scheme.Modules.pushforward e.hom).obj M
  let q : (Scheme.Modules.pushforward e.inv).obj N ≅ M :=
    (Scheme.Modules.pushforwardComp e.hom e.inv).app M ≪≫
      (Scheme.Modules.pushforwardCongr e.hom_inv_id).app M ≪≫
      (Scheme.Modules.pushforwardId X).app M
  let j : N ≅ M.restrict e.inv :=
    ((Scheme.Modules.restrictFunctorAdjCounitIso e.inv).app N).symm ≪≫
      (Scheme.Modules.restrictFunctor e.inv).mapIso q
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso j.symm inferInstance

abbrev affineToSpecModule [IsAffine X] (M : X.Modules) :=
  (Scheme.Modules.pushforward X.toSpecΓ).obj M

instance affineToSpecModule_quasicoherent [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] : (affineToSpecModule M).IsQuasicoherent :=
  quasicoherent_pushforward_iso X.isoSpec M

theorem affine_sections_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) :
    IsLocalizedModule.Away r
      (((modulesSpecToSheaf.obj (affineToSpecModule M)).obj.map
        (PrimeSpectrum.basicOpen r).leTop.op).hom) :=
  ((isIso_fromTildeΓ_iff_isLocalizing (affineToSpecModule M)).mp inferInstance) r

def affineSpecSections [IsAffine X] (M : X.Modules)
    (U : (Spec Γ(X,⊤)).Opens) :
    ((modulesSpecToSheaf.obj (affineToSpecModule M)).obj.obj (op U)) ≃ₗ[Γ(X,⊤)]
      OpenSections M (X.toSpecΓ ⁻¹ᵁ U) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    let : Module Γ(X,X.toSpecΓ ⁻¹ᵁ U) Γ(M,X.toSpecΓ ⁻¹ᵁ U) :=
      (M.val.obj (op (X.toSpecΓ ⁻¹ᵁ U))).isModule
    change @SMul.smul Γ(X,X.toSpecΓ ⁻¹ᵁ U) Γ(M,X.toSpecΓ ⁻¹ᵁ U) _
      ((X.toSpecΓ.app U).hom
        ((Spec Γ(X,⊤)).presheaf.map U.leTop.op ((Scheme.ΓSpecIso Γ(X,⊤)).inv r))) m =
      @SMul.smul Γ(X,X.toSpecΓ ⁻¹ᵁ U) Γ(M,X.toSpecΓ ⁻¹ᵁ U) _
        (restrictScalar X (X.toSpecΓ ⁻¹ᵁ U) r) m
    congr 1
    have h := congrArg (fun f : Γ(Spec Γ(X,⊤),⊤) ⟶ Γ(X,X.toSpecΓ ⁻¹ᵁ U) =>
      f ((Scheme.ΓSpecIso Γ(X,⊤)).inv r)) (X.toSpecΓ.naturality U.leTop.op)
    simp only [CommRingCat.comp_apply, Scheme.toSpecΓ_appTop] at h
    change _ = restrictScalar X (X.toSpecΓ ⁻¹ᵁ U)
      ((Scheme.ΓSpecIso Γ(X,⊤)).hom ((Scheme.ΓSpecIso Γ(X,⊤)).inv r)) at h
    rw [(Scheme.ΓSpecIso Γ(X,⊤)).inv_hom_id_apply r] at h
    exact h

def openSectionsCongr (M : X.Modules) {U V : X.Opens} (h : U = V) :
    OpenSections M U ≃ₗ[Γ(X,⊤)] OpenSections M V := by
  subst V
  exact LinearEquiv.refl _ _

lemma openSectionsCongr_restriction (M : X.Modules) {U V : X.Opens} (h : U = V)
    (m : OpenSections M ⊤) :
    openSectionsCongr M h (openRestriction M (show U ≤ ⊤ from le_top) m) = openRestriction M (show V ≤ ⊤ from le_top) m := by
  subst V
  rfl

theorem affine_openRestriction_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) :
    IsLocalizedModule.Away r (openRestriction M (X.basicOpen_le r)) := by
  let F := modulesSpecToSheaf.obj (affineToSpecModule M)
  let f := (F.obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom
  let e0 : (F.obj.obj (op ⊤)) ≃ₗ[Γ(X,⊤)] OpenSections M ⊤ := affineSpecSections M ⊤
  let e1 := (affineSpecSections M (PrimeSpectrum.basicOpen r)).trans
    (openSectionsCongr M (Scheme.toSpecΓ_preimage_basicOpen X r))
  have hf : IsLocalizedModule.Away r f := affine_sections_localize M r
  have hq : IsLocalizedModule.Away r (e1.toLinearMap ∘ₗ f ∘ₗ e0.symm.toLinearMap) := by
    let := hf
    let := IsLocalizedModule.of_linearEquiv (.powers r) f e1
    exact IsLocalizedModule.of_linearEquiv_right (.powers r) (e1.toLinearMap ∘ₗ f) e0.symm
  have he : e1.toLinearMap ∘ₗ f ∘ₗ e0.symm.toLinearMap =
      openRestriction M (X.basicOpen_le r) := by
    ext m
    exact openSectionsCongr_restriction M (Scheme.toSpecΓ_preimage_basicOpen X r) m
  rwa [he] at hq

theorem affine_basicOpen_denominators [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (x : OpenSections M (X.basicOpen r)) :
    ∃ n : ℕ, ∃ y : OpenSections M ⊤,
      openRestriction M (X.basicOpen_le r) y = r^n • x := by
  let f := openRestriction M (X.basicOpen_le r)
  let : IsLocalizedModule.Away r f := affine_openRestriction_localize M r
  obtain ⟨n,y,hy⟩ := (inferInstance : IsLocalizedModule.Away r f).surj _ _ x
  exact ⟨n,y,hy.symm⟩

def openTopSections (M : X.Modules) :
    letI : Module Γ(X,⊤) Γ(M,⊤) := (M.val.obj (op ⊤)).isModule
    OpenSections M ⊤ ≃ₗ[Γ(X,⊤)] Γ(M,⊤) := by
  letI : Module Γ(X,⊤) Γ(M,⊤) := (M.val.obj (op ⊤)).isModule
  refine { toFun := fun x => x
           invFun := fun x => x
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro r m
  change @SMul.smul Γ(X,⊤) Γ(M,⊤) _ (restrictScalar X ⊤ r) m =
    @SMul.smul Γ(X,⊤) Γ(M,⊤) _ r m
  congr 1
  change (X.presheaf.map (𝟙 (op ⊤))) r = r
  rw [X.presheaf.map_id]
  rfl

lemma restrictScalar_appIso (f : Y ⟶ X) [IsOpenImmersion f] (U : Y.Opens)
    (r : Γ(X,⊤)) :
    (f.appIso U).inv (restrictScalar Y U (f.appTop r)) =
      restrictScalar X (f ''ᵁ U) r := by
  have h := congrArg (fun g : Γ(X,⊤) ⟶ Γ(X,f ''ᵁ U) => g r)
    (Scheme.Hom.appLE_appIso_inv f (U := ⊤) (V := U) (by simp))
  change (f.appIso U).inv ((f.appLE ⊤ U (by simp)) r) = _ at h
  have he : f.appLE ⊤ U (by simp) = f.appTop ≫ Y.presheaf.map U.leTop.op := by
    erw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  rw [he] at h
  exact h

def restrictedOpenSections (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    (U : Y.Opens) :
    letI := Module.compHom (OpenSections (M.restrict f) U) f.appTop.hom
    OpenSections (M.restrict f) U ≃ₗ[Γ(X,⊤)] OpenSections M (f ''ᵁ U) := by
  letI := Module.compHom (OpenSections (M.restrict f) U) f.appTop.hom
  letI : Module Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) := (M.val.obj (op (f ''ᵁ U))).isModule
  refine { toFun := fun x => x
           invFun := fun x => x
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro r m
  change @SMul.smul Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) _
      ((f.appIso U).inv (restrictScalar Y U (f.appTop r))) m =
    @SMul.smul Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) _ (restrictScalar X (f ''ᵁ U) r) m
  rw [restrictScalar_appIso]

lemma restrictedOpenSections_naturality (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    {U V : Y.Opens} (h : U ≤ V) (m : OpenSections (M.restrict f) V) :
    restrictedOpenSections M f U (openRestriction (M.restrict f) h m) =
      openRestriction M (f.image_mono h) (restrictedOpenSections M f V m) := rfl

theorem affine_basicOpen_zero [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (x : OpenSections M ⊤)
    (hx : openRestriction M (X.basicOpen_le r) x = 0) :
    ∃ N : ℕ, ∀ n ≥ N, r ^ n • x = 0 := by
  let := affine_openRestriction_localize M r
  obtain ⟨⟨_, N, rfl⟩, hN⟩ :=
    (IsLocalizedModule.eq_zero_iff (.powers r)
      (openRestriction M (X.basicOpen_le r))).mp hx
  change r ^ N • x = 0 at hN
  refine ⟨N, fun n hn => ?_⟩
  rw [← Nat.sub_add_cancel hn, pow_add, mul_smul, hN, smul_zero]

lemma openRestriction_comp_apply (M : X.Modules) {U V W : X.Opens}
    (hUV : U ≤ V) (hVW : V ≤ W) (x : OpenSections M W) :
    openRestriction M hUV (openRestriction M hVW x) =
      openRestriction M (hUV.trans hVW) x := by
  change M.presheaf.map _ (M.presheaf.map _ x) = M.presheaf.map _ x
  erw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp]

lemma openRestriction_zero_congr (M : X.Modules) {U V W : X.Opens}
    (e : U = V) (hU : U ≤ W) (hV : V ≤ W) (x : OpenSections M W)
    (h : openRestriction M hU x = 0) : openRestriction M hV x = 0 := by
  subst V
  exact h

lemma affine_immersion_zero_on [IsAffine Y] (M : X.Modules) [M.IsQuasicoherent]
    (f : Y ⟶ X) [IsOpenImmersion f] (r : Γ(X,⊤))
    (U : X.Opens) (hU : f ''ᵁ (⊤ : Y.Opens) ≤ U) (x : OpenSections M U)
    (hx : openRestriction M (show U ⊓ X.basicOpen r ≤ U from inf_le_left) x = 0) :
    ∃ N : ℕ, ∀ n ≥ N,
      openRestriction M hU (r ^ n • x) = 0 := by
  let x' := (restrictedOpenSections M f ⊤).symm
    (openRestriction M hU x)
  have hWD : f ''ᵁ (Y.basicOpen (f.appTop r)) ≤ U ⊓ X.basicOpen r := by
    apply le_inf
    · exact (f.image_mono le_top).trans hU
    · rw [← Scheme.preimage_basicOpen_top]
      exact f.image_preimage_le _
  have hx' : openRestriction (M.restrict f) (Y.basicOpen_le (f.appTop r)) x' = 0 := by
    apply (restrictedOpenSections M f _).injective
    rw [map_zero, restrictedOpenSections_naturality]
    simp only [x', LinearEquiv.apply_symm_apply]
    rw [openRestriction_comp_apply]
    rw [← openRestriction_comp_apply M hWD (show U ⊓ X.basicOpen r ≤ U from inf_le_left) x, hx, map_zero]
  obtain ⟨N, hN⟩ := affine_basicOpen_zero (M.restrict f) (f.appTop r) x' hx'
  refine ⟨N, fun n hn => ?_⟩
  have hi := congrArg (restrictedOpenSections M f ⊤) (hN n hn)
  let : Module Γ(X,⊤) (OpenSections (M.restrict f) ⊤) :=
    Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  have hscalar : (f.appTop r) ^ n • x' = (r ^ n) • x' := by
    change (f.appTop r) ^ n • x' = f.appTop (r ^ n) • x'
    rw [map_pow]
  rw [hscalar, map_smul, map_zero] at hi
  simpa only [x', LinearEquiv.apply_symm_apply, map_smul] using hi

theorem compact_open_section_zero (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (U : X.Opens) (hU : IsCompact (U : Set X))
    (x : OpenSections M U)
    (hx : openRestriction M (show U ⊓ X.basicOpen r ≤ U from inf_le_left) x = 0) :
    ∃ N : ℕ, ∀ n ≥ N, r ^ n • x = 0 := by
  classical
  obtain ⟨s, hs, e⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
    ⟨hU, U.2⟩
  replace e : U = iSup fun i : s => (i : X.Opens) := by
    ext1
    simpa using e
  have h₁ (i : s) : i.1.1 ≤ U := by
    rw [e]
    exact le_iSup (fun i : s => (i : X.Opens)) i
  have H (i : s) : ∃ N : ℕ, ∀ n ≥ N,
      openRestriction M (h₁ i) (r ^ n • x) = 0 := by
    let : IsAffine i.1.1.toScheme := i.1.2
    have hh := affine_immersion_zero_on M i.1.1.ι r U
      (by simpa only [Scheme.Opens.ι_image_top] using h₁ i) x hx
    obtain ⟨N, hN⟩ := hh
    exact ⟨N, fun n hn => openRestriction_zero_congr M i.1.1.ι_image_top _ _ _ (hN n hn)⟩
  choose n hn using H
  have := hs.to_subtype
  let := Fintype.ofFinite s
  refine ⟨Finset.univ.sup n, fun k hk => ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i : s => (i : X.Opens)) U
    (fun i => homOfLE (h₁ i)) (by rw [e])
  intro i
  have hi := hn i k ((Finset.le_sup (f := n) (Finset.mem_univ i)).trans hk)
  change M.presheaf.map _ (r ^ k • x) = M.presheaf.map _ 0
  rw [map_zero]
  exact hi

theorem global_section_zero [CompactSpace X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (x : OpenSections M ⊤)
    (hx : openRestriction M (X.basicOpen_le r) x = 0) :
    ∃ N : ℕ, ∀ n ≥ N, r ^ n • x = 0 := by
  apply compact_open_section_zero M r ⊤ isCompact_univ x
  exact openRestriction_zero_congr M (top_inf_eq (a := X.basicOpen r)).symm _ _ _ hx

lemma openSectionsCongr_naturality (M : X.Modules) {U V U' V' : X.Opens}
    (eU : U = U') (eV : V = V') (h : U ≤ V) (h' : U' ≤ V')
    (x : OpenSections M V) :
    openSectionsCongr M eU (openRestriction M h x) =
      openRestriction M h' (openSectionsCongr M eV x) := by
  subst U' V'
  rfl

lemma principal_open_image (r : Γ(X,⊤)) (U : X.Opens) :
    U.ι ''ᵁ U.toScheme.basicOpen (U.ι.appTop r) = U ⊓ X.basicOpen r := by
  rw [← Scheme.preimage_basicOpen_top, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]

def affineOpenPrincipalEquiv (M : X.Modules) (r : Γ(X,⊤)) (U : X.Opens) :
    letI := Module.compHom (OpenSections (M.restrict U.ι)
      (U.toScheme.basicOpen (U.ι.appTop r))) U.ι.appTop.hom
    OpenSections (M.restrict U.ι) (U.toScheme.basicOpen (U.ι.appTop r)) ≃ₗ[Γ(X,⊤)]
      OpenSections M (U ⊓ X.basicOpen r) :=
  (restrictedOpenSections M U.ι _).trans (openSectionsCongr M (principal_open_image r U))

def affineOpenTopEquiv (M : X.Modules) (U : X.Opens) :
    letI := Module.compHom (OpenSections (M.restrict U.ι) ⊤) U.ι.appTop.hom
    OpenSections (M.restrict U.ι) ⊤ ≃ₗ[Γ(X,⊤)] OpenSections M U :=
  (restrictedOpenSections M U.ι ⊤).trans (openSectionsCongr M U.ι_image_top)

lemma affineOpenPrincipalEquiv_restrict (M : X.Modules) (r : Γ(X,⊤)) (U : X.Opens)
    (y : OpenSections (M.restrict U.ι) ⊤) :
    affineOpenPrincipalEquiv M r U
      (openRestriction (M.restrict U.ι) (U.toScheme.basicOpen_le (U.ι.appTop r)) y) =
    openRestriction M (show U ⊓ X.basicOpen r ≤ U from inf_le_left)
      (affineOpenTopEquiv M U y) := by
  dsimp only [affineOpenPrincipalEquiv, affineOpenTopEquiv, LinearEquiv.trans_apply]
  rw [restrictedOpenSections_naturality]
  exact openSectionsCongr_naturality M (principal_open_image r U) U.ι_image_top _ _ _

theorem affine_open_section_extends (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (U : X.Opens) (hU : IsAffineOpen U)
    (x : OpenSections M (U ⊓ X.basicOpen r)) :
    ∃ n : ℕ, ∃ y : OpenSections M U,
      openRestriction M (show U ⊓ X.basicOpen r ≤ U from inf_le_left) y = r ^ n • x := by
  let : IsAffine U.toScheme := hU
  let : Module Γ(X,⊤) (OpenSections (M.restrict U.ι)
      (U.toScheme.basicOpen (U.ι.appTop r))) :=
    Module.compHom _ U.ι.appTop.hom
  let x' := (affineOpenPrincipalEquiv M r U).symm x
  obtain ⟨n, y, hy⟩ := affine_basicOpen_denominators (M.restrict U.ι) (U.ι.appTop r) x'
  refine ⟨n, affineOpenTopEquiv M U y, ?_⟩
  have hscalar : (U.ι.appTop r) ^ n • x' = (r ^ n) • x' := by
    change (U.ι.appTop r) ^ n • x' = U.ι.appTop (r ^ n) • x'
    rw [map_pow]
  have hh := congrArg (affineOpenPrincipalEquiv M r U) hy
  rw [hscalar, map_smul, affineOpenPrincipalEquiv_restrict] at hh
  simpa only [x', LinearEquiv.apply_symm_apply] using hh

def overlapDifference (M : X.Modules) {U V : X.Opens}
    (y : OpenSections M U) (z : OpenSections M V) : OpenSections M (U ⊓ V) :=
  openRestriction M inf_le_left y - openRestriction M inf_le_right z

lemma overlapDifference_restrict_zero (M : X.Modules) (r : Γ(X,⊤))
    (x : OpenSections M (X.basicOpen r)) (N : ℕ) {U V : X.Opens}
    (y : OpenSections M U) (z : OpenSections M V)
    (hy : openRestriction M (show U ⊓ X.basicOpen r ≤ U from inf_le_left) y =
      r ^ N • openRestriction M inf_le_right x)
    (hz : openRestriction M (show V ⊓ X.basicOpen r ≤ V from inf_le_left) z =
      r ^ N • openRestriction M inf_le_right x) :
    openRestriction M (show (U ⊓ V) ⊓ X.basicOpen r ≤ U ⊓ V from inf_le_left)
      (overlapDifference M y z) = 0 := by
  have hU : (U ⊓ V) ⊓ X.basicOpen r ≤ U ⊓ X.basicOpen r := inf_le_inf inf_le_left le_rfl
  have hV : (U ⊓ V) ⊓ X.basicOpen r ≤ V ⊓ X.basicOpen r := inf_le_inf inf_le_right le_rfl
  calc
    _ = openRestriction M hU (openRestriction M inf_le_left y) -
        openRestriction M hV (openRestriction M inf_le_left z) := by
      simp only [overlapDifference, map_sub, openRestriction_comp_apply]
    _ = 0 := by
      rw [hy, hz, map_smul, map_smul, openRestriction_comp_apply, openRestriction_comp_apply,
        sub_self]

lemma overlapDifference_smul_zero_iff (M : X.Modules) (r : Γ(X,⊤))
    {U V : X.Opens} (y : OpenSections M U) (z : OpenSections M V) (K : ℕ) :
    r ^ K • overlapDifference M y z = 0 ↔
      openRestriction M (show U ⊓ V ≤ U from inf_le_left) (r ^ K • y) =
      openRestriction M (show U ⊓ V ≤ V from inf_le_right) (r ^ K • z) := by
  simp only [overlapDifference, smul_sub, map_smul, sub_eq_zero]

theorem clear_finite_overlap_discrepancies (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) {ι : Type*} [Fintype ι] (U : ι → X.Opens)
    (hcompact : ∀ i j, IsCompact ((U i ⊓ U j : X.Opens) : Set X))
    (x : OpenSections M (X.basicOpen r)) (N : ℕ) (y : ∀ i, OpenSections M (U i))
    (hy : ∀ i, openRestriction M (show U i ⊓ X.basicOpen r ≤ U i from inf_le_left) (y i) =
      r ^ N • openRestriction M inf_le_right x) :
    ∃ K : ℕ, ∀ i j,
      openRestriction M (show U i ⊓ U j ≤ U i from inf_le_left) (r ^ K • y i) =
      openRestriction M (show U i ⊓ U j ≤ U j from inf_le_right) (r ^ K • y j) := by
  classical
  have h (ij : ι × ι) := compact_open_section_zero M r (U ij.1 ⊓ U ij.2)
    (hcompact ij.1 ij.2) (overlapDifference M (y ij.1) (y ij.2))
    (overlapDifference_restrict_zero M r x N _ _ (hy ij.1) (hy ij.2))
  choose k hk using h
  let K := Finset.univ.sup k
  refine ⟨K, fun i j => ?_⟩
  apply (overlapDifference_smul_zero_iff M r (y i) (y j) K).mp
  exact hk (i,j) K (Finset.le_sup (f := k) (Finset.mem_univ (i,j)))

lemma restriction_of_glued_power (M : X.Modules) (r : Γ(X,⊤))
    {ι : Type*} (U : ι → X.Opens) (hcover : (⨆ i, U i) = ⊤)
    (x : OpenSections M (X.basicOpen r)) (N K : ℕ) (y : ∀ i, OpenSections M (U i))
    (hy : ∀ i, openRestriction M (show U i ⊓ X.basicOpen r ≤ U i from inf_le_left) (y i) =
      r ^ N • openRestriction M inf_le_right x)
    (z : OpenSections M ⊤)
    (hz : ∀ i, openRestriction M (show U i ≤ ⊤ from le_top) z = r ^ K • y i) :
    openRestriction M (X.basicOpen_le r) z = r ^ (N + K) • x := by
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i => U i ⊓ X.basicOpen r)
    (X.basicOpen r) (fun i => homOfLE inf_le_right)
    (by rw [← iSup_inf_eq, hcover, top_inf_eq])
  intro i
  change openRestriction M inf_le_right (openRestriction M (X.basicOpen_le r) z) =
    openRestriction M inf_le_right (r ^ (N + K) • x)
  rw [openRestriction_comp_apply,
    ← openRestriction_comp_apply M (show U i ⊓ X.basicOpen r ≤ U i from inf_le_left) le_top z,
    hz i, map_smul, hy i, map_smul, ← mul_smul, ← pow_add, Nat.add_comm K N]

theorem finite_cover_power_gluing (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) {ι : Type*} [Fintype ι] (U : ι → X.Opens)
    (hcover : (⨆ i, U i) = ⊤)
    (hcompact : ∀ i j, IsCompact ((U i ⊓ U j : X.Opens) : Set X))
    (x : OpenSections M (X.basicOpen r)) (N : ℕ) (y : ∀ i, OpenSections M (U i))
    (hy : ∀ i, openRestriction M (show U i ⊓ X.basicOpen r ≤ U i from inf_le_left) (y i) =
      r ^ N • openRestriction M inf_le_right x) :
    ∃ K : ℕ, ∃ z : OpenSections M ⊤,
      openRestriction M (X.basicOpen_le r) z = r ^ (N + K) • x := by
  obtain ⟨K, hK⟩ := clear_finite_overlap_discrepancies M r U hcompact x N y hy
  have hh := TopCat.Sheaf.existsUnique_gluing' ⟨_, M.isSheaf⟩ U ⊤
    (fun i => homOfLE (show U i ≤ ⊤ from le_top)) (by rw [hcover]) (fun i => r ^ K • y i) ?_
  · obtain ⟨z, hz, _⟩ := hh
    exact ⟨K, z, restriction_of_glued_power M r U hcover x N K y hy z hz⟩
  · intro i j
    exact hK i j

theorem finite_affine_local_extensions (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) {ι : Type*} [Fintype ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (x : OpenSections M (X.basicOpen r)) :
    ∃ N : ℕ, ∃ y : ∀ i, OpenSections M (U i),
      ∀ i, openRestriction M (show U i ⊓ X.basicOpen r ≤ U i from inf_le_left) (y i) =
        r ^ N • openRestriction M inf_le_right x := by
  classical
  choose n y hy using fun i => affine_open_section_extends M r (U i) (hU i)
    (openRestriction M (show U i ⊓ X.basicOpen r ≤ X.basicOpen r from inf_le_right) x)
  let N := Finset.univ.sup n
  refine ⟨N, fun i => r ^ (N - n i) • y i, fun i => ?_⟩
  rw [map_smul, hy i, ← mul_smul, ← pow_add,
    Nat.sub_add_cancel (Finset.le_sup (f := n) (Finset.mem_univ i))]

theorem global_section_extends [NoetherianSpace X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (x : OpenSections M (X.basicOpen r)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : OpenSections M ⊤,
      openRestriction M (X.basicOpen_le r) y = r ^ n • x := by
  classical
  obtain ⟨s, hs, e⟩ :=
    (isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens (X := X)
      (U := ((⊤ : X.Opens) : Set X))).mp
      ⟨NoetherianSpace.isCompact _, (⊤ : X.Opens).2⟩
  have hcover : (⨆ i : s, (i : X.Opens)) = ⊤ := by
    ext1
    simpa using e.symm
  have := hs.to_subtype
  let := Fintype.ofFinite s
  obtain ⟨N, y, hy⟩ := finite_affine_local_extensions M r (fun i : s => (i : X.Opens))
    (fun i => i.1.2) x
  obtain ⟨K, z, hz⟩ := finite_cover_power_gluing M r (fun i : s => (i : X.Opens)) hcover
    (fun i j => NoetherianSpace.isCompact _) x N y hy
  refine ⟨N + K, fun n hn => ⟨r ^ (n - (N + K)) • z, ?_⟩⟩
  rw [map_smul, hz, ← mul_smul, ← pow_add, Nat.sub_add_cancel hn]

theorem global_section_extends_native [NoetherianSpace X]
    (M : X.Modules) [M.IsQuasicoherent] (r : Γ(X,⊤)) (x : Γ(M, X.basicOpen r)) :
    letI : Module Γ(X, X.basicOpen r) Γ(M, X.basicOpen r) :=
      (M.val.obj (op (X.basicOpen r))).isModule
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : Γ(M,⊤),
      M.presheaf.map (homOfLE (X.basicOpen_le r)).op y =
        (restrictScalar X (X.basicOpen r) r) ^ n • x := by
  let : Module Γ(X, X.basicOpen r) Γ(M, X.basicOpen r) :=
    (M.val.obj (op (X.basicOpen r))).isModule
  obtain ⟨N, hN⟩ := global_section_extends M r x
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨y, hy⟩ := hN n hn
  refine ⟨y, ?_⟩
  change M.presheaf.map (homOfLE (X.basicOpen_le r)).op y =
    (restrictScalar X (X.basicOpen r) (r ^ n)) • x at hy
  simpa only [map_pow] using hy

theorem global_section_zero_native [CompactSpace X]
    (M : X.Modules) [M.IsQuasicoherent] (r : Γ(X,⊤)) (x : Γ(M,⊤))
    (hx : M.presheaf.map (homOfLE (X.basicOpen_le r)).op x = 0) :
    letI : Module Γ(X,⊤) Γ(M,⊤) := (M.val.obj (op ⊤)).isModule
    ∃ N : ℕ, ∀ n ≥ N, r ^ n • x = 0 := by
  let : Module Γ(X,⊤) Γ(M,⊤) := (M.val.obj (op ⊤)).isModule
  obtain ⟨N, hN⟩ := global_section_zero M r x hx
  refine ⟨N, fun n hn => ?_⟩
  have hh := hN n hn
  change restrictScalar X ⊤ (r ^ n) • x = 0 at hh
  have hr : restrictScalar X ⊤ (r ^ n) = r ^ n := by
    change X.presheaf.map (𝟙 (op ⊤)) (r ^ n) = r ^ n
    rw [X.presheaf.map_id]
    rfl
  exact (congrArg (fun c : Γ(X, ⊤) => c • x) hr).symm.trans hh

end
end PiExponent.GlobalSectionClearing

end OAI
