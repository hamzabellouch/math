import OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology
import OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace PiExponent.CoherentTwist

universe u
variable {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]

abbrev affineSections (U : (Spec R).Opens) :=
  (modulesSpecToSheaf.obj M).obj.obj (op U)

abbrev principalRestriction (r : R) :=
  ((modulesSpecToSheaf.obj M).obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom

theorem principalRestriction_localizes (r : R) :
    IsLocalizedModule.Away r (principalRestriction M r) :=
  ((isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance) r

theorem principal_section_extends (r : R)
    (x : affineSections M (PrimeSpectrum.basicOpen r)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : affineSections M ⊤,
      principalRestriction M r y = r ^ n • x := by
  let := principalRestriction_localizes M r
  obtain ⟨N, y, hy⟩ := (inferInstance : IsLocalizedModule.Away r
    (principalRestriction M r)).surj _ _ x
  refine ⟨N, fun n hn => ⟨r ^ (n - N) • y, ?_⟩⟩
  rw [map_smul, ← hy, ← mul_smul, ← pow_add, Nat.sub_add_cancel hn]

theorem principal_section_zero (r : R) (x : affineSections M ⊤)
    (hx : principalRestriction M r x = 0) :
    ∃ N : ℕ, ∀ n ≥ N, r ^ n • x = 0 := by
  let := principalRestriction_localizes M r
  obtain ⟨⟨_, N, rfl⟩, hN⟩ :=
    (IsLocalizedModule.eq_zero_iff (.powers r) (principalRestriction M r)).mp hx
  change r ^ N • x = 0 at hN
  refine ⟨N, fun n hn => ?_⟩
  rw [← Nat.sub_add_cancel hn, pow_add, mul_smul, hN, smul_zero]

theorem finite_principal_sections_extend {ι : Type*} [Fintype ι] (r : R)
    (x : ι → affineSections M (PrimeSpectrum.basicOpen r)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : ι → affineSections M ⊤,
      ∀ i, principalRestriction M r (y i) = r ^ n • x i := by
  classical
  choose N hN using fun i => principal_section_extends M r (x i)
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  have hn' (i : ι) : N i ≤ n :=
    (Finset.le_sup (f := N) (Finset.mem_univ i)).trans hn
  choose y hy using fun i => hN i n (hn' i)
  exact ⟨y, hy⟩

theorem finite_principal_sections_zero {ι : Type*} [Fintype ι] (r : R)
    (x : ι → affineSections M ⊤)
    (hx : ∀ i, principalRestriction M r (x i) = 0) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ i, r ^ n • x i = 0 := by
  classical
  choose N hN using fun i => principal_section_zero M r (x i) (hx i)
  refine ⟨Finset.univ.sup N, fun n hn i => ?_⟩
  exact hN i n ((Finset.le_sup (f := N) (Finset.mem_univ i)).trans hn)

open TopologicalSpace
variable {X : Scheme.{u}} {P Q : X.Modules}

lemma app_zero_of_restrict (φ : P ⟶ Q) (U W : X.Opens) (hW : W ≤ U)
    (h : (Scheme.Modules.restrictFunctor U.ι).map φ = 0) : φ.app W = 0 := by
  have hz := congrArg (fun q : P.restrict U.ι ⟶ Q.restrict U.ι =>
    q.app (U.ι ⁻¹ᵁ W)) h
  have he : U.ι ''ᵁ U.ι ⁻¹ᵁ W = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hW]
  change φ.app (U.ι ''ᵁ U.ι ⁻¹ᵁ W) = 0 at hz
  suffices hh : ∀ A : X.Opens, A = W → φ.app A = 0 → φ.app W = 0 from hh _ he hz
  intro A hA hφ
  subst A
  exact hφ

lemma eq_zero_of_local (φ : P ⟶ Q)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      (Scheme.Modules.restrictFunctor U.ι).map φ = 0) : φ = 0 := by
  ext W m
  change φ.app W m = 0
  let F : (X : TopCat).Sheaf AddCommGrpCat := (SheafOfModules.toSheaf X.ringCatSheaf).obj Q
  apply TopCat.Presheaf.section_ext F W (φ.app W m) 0
  intro x hx
  obtain ⟨U,hxU,hU⟩ := h x
  let V : X.Opens := W ⊓ U
  have hv : φ.app V = 0 := app_zero_of_restrict φ U V inf_le_right hU
  change Q.presheaf.germ W x hx (φ.app W m) = Q.presheaf.germ W x hx 0
  rw [← TopCat.Presheaf.germ_res_apply Q.presheaf (homOfLE (show V ≤ W from inf_le_left))
    x (show x ∈ V from ⟨hx,hxU⟩)]
  have hn := CategoryTheory.congr_fun (φ.mapPresheaf.naturality
    (homOfLE (show V ≤ W from inf_le_left)).op) m
  change φ.app V (P.presheaf.map (homOfLE inf_le_left).op m) =
    Q.presheaf.map (homOfLE inf_le_left).op (φ.app W m) at hn
  rw [← hn,hv]
  simp

lemma epi_of_local (φ : P ⟶ Q)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Epi ((Scheme.Modules.restrictFunctor U.ι).map φ)) : Epi φ := by
  apply (Preadditive.epi_iff_cancel_zero _).mpr
  intro T g hg
  apply eq_zero_of_local
  intro x
  obtain ⟨U,hx,hU⟩ := h x
  let := hU
  refine ⟨U,hx,?_⟩
  apply (cancel_epi ((Scheme.Modules.restrictFunctor U.ι).map φ)).mp
  rw [← Functor.map_comp,hg,Functor.map_zero,comp_zero]

lemma mono_of_local (φ : P ⟶ Q)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Mono ((Scheme.Modules.restrictFunctor U.ι).map φ)) : Mono φ := by
  apply (Preadditive.mono_iff_cancel_zero _).mpr
  intro T g hg
  apply eq_zero_of_local
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  let := hU
  refine ⟨U, hx, ?_⟩
  apply (cancel_mono ((Scheme.Modules.restrictFunctor U.ι).map φ)).mp
  rw [← Functor.map_comp, hg, Functor.map_zero, zero_comp]

lemma exact_of_local (S : ShortComplex X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      (S.map (Scheme.Modules.restrictFunctor U.ι)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  apply (IsZero.iff_id_eq_zero _).mpr
  apply eq_zero_of_local
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  have hz : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj S.homology) :=
    ((ShortComplex.exact_iff_isZero_homology _).mp hU).of_iso
      (S.mapHomologyIso (Scheme.Modules.restrictFunctor U.ι)).symm
  refine ⟨U, hx, ?_⟩
  rw [CategoryTheory.Functor.map_id]
  exact hz.eq_of_src _ _

end PiExponent.CoherentTwist

namespace PiExponentSeshadri.Geometry
open MonoidalCategory
variable {X : Scheme}

private lemma tensorRestrict_natural {C D : Type*} [Category C] [Category D]
    [mC : MonoidalCategory C] [mD : MonoidalCategory D] (R F : C ⥤ D) [F.OplaxMonoidal]
    (e : R ≅ F) {M N P Q : C} (f : M ⟶ N) (g : P ⟶ Q) :
    R.map (f ⊗ₘ g) ≫ (e.hom.app (N ⊗ Q) ≫
      Functor.OplaxMonoidal.δ F N Q ≫ (e.inv.app N ⊗ₘ e.inv.app Q)) =
    (e.hom.app (M ⊗ P) ≫ Functor.OplaxMonoidal.δ F M P ≫
      (e.inv.app M ⊗ₘ e.inv.app P)) ≫ (R.map f ⊗ₘ R.map g) := by
  rw [← Category.assoc, e.hom.naturality, Category.assoc,
    ← Category.assoc (F.map (f ⊗ₘ g)), ← Functor.OplaxMonoidal.δ_natural,
    Category.assoc, tensorHom_comp_tensorHom, e.inv.naturality,
    e.inv.naturality, ← tensorHom_comp_tensorHom]
  simp only [Category.assoc]

private lemma modulePresheafTensorRestrict_natural_aux (U : X.Opens)
    {M N P Q : PresheafOfModules X.ringCatSheaf.obj}
    (f : M ⟶ N) (g : P ⟶ Q) :
    type_of% (tensorRestrict_natural
    (C := PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (D := PresheafOfModules
      ((U.ι.opensFunctor.op ⋙ X.presheaf) ⋙ forget₂ CommRingCat RingCat))
    (mC := PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf))
    (mD := PresheafOfModulesOfCommRing.monoidalCategory
      (R := U.ι.opensFunctor.op ⋙ X.presheaf))
    (modulePresheafRestrict U.ι)
    (PresheafOfModules.pushforward₀OfCommRingCat U.ι.opensFunctor X.presheaf)
    (modulePresheafRestrictOpensIso U) f g) :=
  tensorRestrict_natural
    (C := PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (D := PresheafOfModules
      ((U.ι.opensFunctor.op ⋙ X.presheaf) ⋙ forget₂ CommRingCat RingCat))
    (mC := PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf))
    (mD := PresheafOfModulesOfCommRing.monoidalCategory
      (R := U.ι.opensFunctor.op ⋙ X.presheaf))
    (modulePresheafRestrict U.ι)
    (PresheafOfModules.pushforward₀OfCommRingCat U.ι.opensFunctor X.presheaf)
    (modulePresheafRestrictOpensIso U) f g

lemma modulePresheafTensorRestrict_natural (U : X.Opens)
    {M N P Q : PresheafOfModules X.ringCatSheaf.obj}
    (f : M ⟶ N) (g : P ⟶ Q) :
    (modulePresheafRestrict U.ι).map
        (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f g) ≫
      (modulePresheafTensorRestrict U N Q).hom =
    (modulePresheafTensorRestrict U M P).hom ≫
      PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := U.toScheme.presheaf)
        ((modulePresheafRestrict U.ι).map f) ((modulePresheafRestrict U.ι).map g) := by
  dsimp only [modulePresheafTensorRestrict, Iso.trans_hom, Iso.symm_hom,
    Functor.Monoidal.μIso_inv, tensorIso_hom]
  exact modulePresheafTensorRestrict_natural_aux U f g

lemma moduleTensorRestrict_natural (U : X.Opens) {M N P Q : X.Modules}
    (f : M ⟶ N) (g : P ⟶ Q) :
    (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap f g) ≫
      (moduleTensorRestrict U N Q).hom =
    (moduleTensorRestrict U M P).hom ≫
      moduleTensorMap ((Scheme.Modules.restrictFunctor U.ι).map f)
        ((Scheme.Modules.restrictFunctor U.ι).map g) := by
  let K : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let R : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
  let Rpre : PresheafOfModules X.ringCatSheaf.obj ⥤
      PresheafOfModules U.toScheme.ringCatSheaf.obj := modulePresheafRestrict U.ι
  let S : PresheafOfModules U.toScheme.ringCatSheaf.obj ⥤ U.toScheme.Modules :=
    PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)
  let e : K ⋙ R ≅ Rpre ⋙ S := moduleSheafificationRestrict U.ι
  let h := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f.val g.val
  let k := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := U.toScheme.presheaf)
    (Rpre.map f.val) (Rpre.map g.val)
  let a := (modulePresheafTensorRestrict U M.val P.val).hom
  let b := (modulePresheafTensorRestrict U N.val Q.val).hom
  change R.map (K.map h) ≫ (e.hom.app _ ≫ S.map b) =
    (e.hom.app _ ≫ S.map a) ≫ S.map k
  have ht : Rpre.map h ≫ b = a ≫ k := modulePresheafTensorRestrict_natural U f.val g.val
  calc
    _ = (R.map (K.map h) ≫ e.hom.app _) ≫ S.map b :=
      (Category.assoc _ _ _).symm
    _ = (e.hom.app _ ≫ S.map (Rpre.map h)) ≫ S.map b :=
      congrArg (· ≫ S.map b) (e.hom.naturality h)
    _ = e.hom.app _ ≫ (S.map (Rpre.map h) ≫ S.map b) := Category.assoc _ _ _
    _ = e.hom.app _ ≫ S.map (Rpre.map h ≫ b) :=
      congrArg (e.hom.app _ ≫ ·) (S.map_comp _ _).symm
    _ = e.hom.app _ ≫ S.map (a ≫ k) :=
      congrArg (fun t => e.hom.app _ ≫ S.map t) ht
    _ = e.hom.app _ ≫ (S.map a ≫ S.map k) :=
      congrArg (e.hom.app _ ≫ ·) (S.map_comp _ _)
    _ = _ := (Category.assoc _ _ _).symm

def moduleTensorRightFunctor (L : X.Modules) : X.Modules ⥤ X.Modules where
  obj M := moduleTensor X M L
  map f := moduleTensorMap f (𝟙 L)
  map_id M := moduleTensorMap_id M L
  map_comp f g := by simpa using moduleTensorMap_comp f g (𝟙 L) (𝟙 L)

@[simp] theorem moduleTensorIso_hom {M N P Q : X.Modules}
    (e : M ≅ N) (f : P ≅ Q) :
    (moduleTensorIso e f).hom = moduleTensorMap e.hom f.hom := rfl

@[reassoc] theorem moduleTensorRightUnit_natural {M N : X.Modules} (f : M ⟶ N) :
    moduleTensorMap f (𝟙 (structureSheaf X)) ≫ (moduleTensorRightUnit N).hom =
      (moduleTensorRightUnit M).hom ≫ f := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let S : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)
  change S.map (f.val ⊗ₘ 𝟙 _) ≫ (S.map (ρ_ N.val).hom ≫ adj.counit.app N) =
    (S.map (ρ_ M.val).hom ≫ adj.counit.app M) ≫ f
  have hu : (f.val ⊗ₘ 𝟙 _) ≫ (ρ_ N.val).hom = (ρ_ M.val).hom ≫ f.val := by
    simpa only [tensorHom_id] using rightUnitor_naturality f.val
  have hS : S.map (f.val ⊗ₘ 𝟙 _) ≫ S.map (ρ_ N.val).hom =
      S.map (ρ_ M.val).hom ≫ S.map f.val :=
    (S.map_comp _ _).symm.trans ((congrArg S.map hu).trans (S.map_comp _ _))
  calc
    _ = (S.map (f.val ⊗ₘ 𝟙 _) ≫ S.map (ρ_ N.val).hom) ≫ adj.counit.app N :=
      (Category.assoc _ _ _).symm
    _ = (S.map (ρ_ M.val).hom ≫ S.map f.val) ≫ adj.counit.app N :=
      congrArg (· ≫ adj.counit.app N) hS
    _ = S.map (ρ_ M.val).hom ≫ (S.map f.val ≫ adj.counit.app N) :=
      Category.assoc _ _ _
    _ = S.map (ρ_ M.val).hom ≫ (adj.counit.app M ≫ f) :=
      congrArg (S.map (ρ_ M.val).hom ≫ ·) (adj.counit.naturality f)
    _ = _ := (Category.assoc _ _ _).symm

def moduleTensorFrame (M : X.Modules) {L : X.Modules}
    (e : L ≅ structureSheaf X) : moduleTensor X M L ≅ M :=
  moduleTensorIso (Iso.refl M) e ≪≫ moduleTensorRightUnit M

@[reassoc] theorem moduleTensorFrame_natural {M N L : X.Modules}
    (f : M ⟶ N) (e : L ≅ structureSheaf X) :
    moduleTensorMap f (𝟙 L) ≫ (moduleTensorFrame N e).hom =
      (moduleTensorFrame M e).hom ≫ f := by
  simp only [moduleTensorFrame, Iso.trans_hom, moduleTensorIso_hom, Iso.refl_hom]
  calc
    _ = moduleTensorMap f e.hom ≫ (moduleTensorRightUnit N).hom := by
      rw [← Category.assoc, ← moduleTensorMap_comp]
      simp only [Category.comp_id, Category.id_comp]
    _ = moduleTensorMap (𝟙 M) e.hom ≫
        moduleTensorMap f (𝟙 (structureSheaf X)) ≫ (moduleTensorRightUnit N).hom := by
      rw [← Category.assoc, ← moduleTensorMap_comp]
      simp only [Category.comp_id, Category.id_comp]
    _ = _ := by rw [moduleTensorRightUnit_natural, Category.assoc]

def moduleTensorRestrictFrame (U : X.Opens) (L : X.Modules)
    (e : L.restrict U.ι ≅ structureSheaf U.toScheme) :
    moduleTensorRightFunctor L ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor U.ι :=
  NatIso.ofComponents
    (fun M => moduleTensorRestrict U M L ≪≫ moduleTensorFrame (M.restrict U.ι) e)
    (by
      intro M N f
      change (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap f (𝟙 L)) ≫
          ((moduleTensorRestrict U N L).hom ≫ (moduleTensorFrame (N.restrict U.ι) e).hom) =
        ((moduleTensorRestrict U M L).hom ≫ (moduleTensorFrame (M.restrict U.ι) e).hom) ≫
          (Scheme.Modules.restrictFunctor U.ι).map f
      rw [← Category.assoc, moduleTensorRestrict_natural, Category.assoc,
        CategoryTheory.Functor.map_id, moduleTensorFrame_natural, Category.assoc])

theorem moduleTensorMap_epi {M N : X.Modules} (f : M ⟶ N) [Epi f]
    (L : LineBundle X) : Epi (moduleTensorMap f (𝟙 L.sheaf)) := by
  apply PiExponent.CoherentTwist.epi_of_local
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  refine ⟨U, hx, ?_⟩
  let F : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
  let E : moduleTensorRightFunctor L.sheaf ⋙ F ≅ F := moduleTensorRestrictFrame U L.sheaf e
  have h : F.map (moduleTensorMap f (𝟙 L.sheaf)) =
      (E.app M).hom ≫ F.map f ≫ (E.app N).inv := by
    exact ((E.app N).eq_comp_inv.mpr (E.hom.naturality f)).trans
      (Category.assoc _ _ _)
  rw [h]
  let : Epi (F.map f) := inferInstanceAs
    (Epi ((Scheme.Modules.restrictFunctor U.ι).map f))
  let : IsIso (E.app M).hom := (E.app M).isIso_hom
  let : IsIso (E.app N).inv := (E.app N).isIso_inv
  exact (inferInstance : Epi (C := U.toScheme.Modules)
    ((E.app M).hom ≫ F.map f ≫ (E.app N).inv))

theorem moduleTensorMap_mono {M N : X.Modules} (f : M ⟶ N) [Mono f]
    (L : LineBundle X) : Mono (moduleTensorMap f (𝟙 L.sheaf)) := by
  apply PiExponent.CoherentTwist.mono_of_local
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  refine ⟨U, hx, ?_⟩
  let F : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
  let E : moduleTensorRightFunctor L.sheaf ⋙ F ≅ F := moduleTensorRestrictFrame U L.sheaf e
  have h : F.map (moduleTensorMap f (𝟙 L.sheaf)) =
      (E.app M).hom ≫ F.map f ≫ (E.app N).inv := by
    exact ((E.app N).eq_comp_inv.mpr (E.hom.naturality f)).trans
      (Category.assoc _ _ _)
  rw [h]
  let : Mono (F.map f) := inferInstanceAs
    (Mono ((Scheme.Modules.restrictFunctor U.ι).map f))
  let : IsIso (E.app M).hom := (E.app M).isIso_hom
  let : IsIso (E.app N).inv := (E.app N).isIso_inv
  exact (inferInstance : Mono (C := U.toScheme.Modules)
    ((E.app M).hom ≫ F.map f ≫ (E.app N).inv))

instance moduleTensorRightFunctor_preservesZero (L : LineBundle X) :
    (moduleTensorRightFunctor L.sheaf).PreservesZeroMorphisms where
  map_zero M N := by
    apply PiExponent.CoherentTwist.eq_zero_of_local
    intro x
    obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
    refine ⟨U, hx, ?_⟩
    let E := moduleTensorRestrictFrame U L.sheaf e
    apply (cancel_mono (E.app N).hom).mp
    rw [zero_comp]
    change ((moduleTensorRightFunctor L.sheaf ⋙ Scheme.Modules.restrictFunctor U.ι).map
      (0 : M ⟶ N)) ≫ E.hom.app N = 0
    rw [E.hom.naturality, CategoryTheory.Functor.map_zero, comp_zero]

theorem moduleTensorRightFunctor_exact (L : LineBundle X)
    (S : ShortComplex X.Modules) (hS : S.Exact) :
    (S.map (moduleTensorRightFunctor L.sheaf)).Exact := by
  apply PiExponent.CoherentTwist.exact_of_local
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  refine ⟨U, hx, ?_⟩
  exact ShortComplex.exact_of_iso
    (S.mapNatIso (moduleTensorRestrictFrame U L.sheaf e)).symm
    (hS.map (Scheme.Modules.restrictFunctor U.ι))

theorem moduleTensorRightFunctor_shortExact (L : LineBundle X)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (moduleTensorRightFunctor L.sheaf)).ShortExact where
  exact := moduleTensorRightFunctor_exact L S hS.exact
  mono_f := by
    have := hS.mono_f
    exact moduleTensorMap_mono S.f L
  epi_g := by
    have := hS.epi_g
    exact moduleTensorMap_epi S.g L

instance moduleTensorRightFunctor_additive (L : LineBundle X) :
    (moduleTensorRightFunctor L.sheaf).Additive where
  map_add {M N} {f g} := by
    apply sub_eq_zero.mp
    apply PiExponent.CoherentTwist.eq_zero_of_local
    intro x
    obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
    refine ⟨U, hx, ?_⟩
    let F := Scheme.Modules.restrictFunctor U.ι
    let T := moduleTensorRightFunctor L.sheaf
    let E := moduleTensorRestrictFrame U L.sheaf e
    have h (a : M ⟶ N) : F.map (T.map a) =
        (E.app M).hom ≫ F.map a ≫ (E.app N).inv := by
      apply (cancel_mono (E.app N).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact E.hom.naturality a
    change F.map (T.map (f + g) - (T.map f + T.map g)) = 0
    rw [F.map_sub, F.map_add, h (f+g), h f, h g, F.map_add,
      Preadditive.add_comp, Preadditive.comp_add, sub_self]

def moduleTwistFunctor (L : LineBundle X) : ℕ → X.Modules ⥤ X.Modules
  | 0 => 𝟭 _
  | n + 1 => moduleTwistFunctor L n ⋙ moduleTensorRightFunctor L.sheaf

instance moduleTwistFunctor_additive (L : LineBundle X) (n : ℕ) :
    (moduleTwistFunctor L n).Additive := by
  induction n with
  | zero => change (𝟭 X.Modules).Additive; infer_instance
  | succ n ih =>
    change (moduleTwistFunctor L n ⋙ moduleTensorRightFunctor L.sheaf).Additive
    infer_instance

theorem moduleTwistFunctor_add (L : LineBundle X) (m n : ℕ) :
    moduleTwistFunctor L (m+n) = moduleTwistFunctor L m ⋙ moduleTwistFunctor L n := by
  induction n with
  | zero =>
    change moduleTwistFunctor L m = moduleTwistFunctor L m ⋙ 𝟭 _
    rfl
  | succ n ih =>
    change moduleTwistFunctor L (m+n) ⋙ moduleTensorRightFunctor L.sheaf =
      moduleTwistFunctor L m ⋙ (moduleTwistFunctor L n ⋙ moduleTensorRightFunctor L.sheaf)
    rw [ih]
    rfl

theorem moduleTwistFunctor_shortExact (L : LineBundle X) (n : ℕ)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (moduleTwistFunctor L n)).ShortExact := by
  induction n with
  | zero => exact hS
  | succ n ih =>
    change ((S.map (moduleTwistFunctor L n)).map
      (moduleTensorRightFunctor L.sheaf)).ShortExact
    exact moduleTensorRightFunctor_shortExact L (S.map (moduleTwistFunctor L n)) ih

def moduleTensorComm (M N : X.Modules) : moduleTensor X M N ≅ moduleTensor X N M := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let : SymmetricCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.symmetricCategory (R := X.presheaf)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (β_ M.val N.val)

def moduleTwistUnitIso (L : LineBundle X) : ∀ n : ℕ,
    (moduleTwistFunctor L n).obj (structureSheaf X) ≅ modulePow X L.sheaf n
  | 0 => Iso.refl _
  | n+1 => moduleTensorIso (moduleTwistUnitIso L n) (Iso.refl L.sheaf) ≪≫
      moduleTensorComm (modulePow X L.sheaf n) L.sheaf

end PiExponentSeshadri.Geometry

end

end OAI
