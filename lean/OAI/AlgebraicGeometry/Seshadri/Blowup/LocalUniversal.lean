import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Blowup.LocalEquations

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry

theorem rees_isBlowup {R : Type} [CommRing R] (I : Ideal R) :
    IsBlowup (IdealPullback.specIdeal I) (ReesGrading.projection I) :=
  ⟨ReesGrading.exceptional_invertible I, fun _ f hf =>
    ReesGrading.affineBlowup_universal I f hf⟩

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open MaximalSeshadri.Geometry
variable {X Y Z : Scheme} {I : X.IdealSheafData} {f : Y ⟶ X}

lemma restricted_image_on_chart (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (h : PresentsPullbackIdeal I f J ι)
    (j : Z ⟶ Y) [IsOpenImmersion j] (U : Z.affineOpens) (V : X.affineOpens)
    (hUV : j ''ᵁ U.1 ≤ f ⁻¹ᵁ V.1) :
    ((restrictedInclusion J ι j).val.app (op U.1)).hom.range =
      ((I.comap f).comap j).ideal U := by
  rw [(I.comap f).ideal_comap_of_isOpenImmersion j U]
  have he := (h.2 ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩ V hUV).trans
    (IdealPullback.comap_ideal I f _ V hUV).symm
  apply Ideal.ext
  intro (r : Γ(Z, U.1))
  change (∃ s, (restrictedInclusion J ι j).val.app (op U.1) s = r) ↔
    (j.appIso U.1).inv r ∈ (I.comap f).ideal
      ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩
  refine Iff.trans ?_ (SetLike.ext_iff.mp he _)
  change (∃ s, _) ↔ ∃ s, ι.val.app (op (j ''ᵁ U.1)) s = (j.appIso U.1).inv r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change (j.appIso U.1).hom (ι.val.app (op (j ''ᵁ U.1)) s) = r at hs
    rw [← hs]
    exact (congrArg (fun k : Γ(Y, j ''ᵁ U.1) ⟶ Γ(Y, j ''ᵁ U.1) =>
      k (ι.val.app (op (j ''ᵁ U.1)) s)) (j.appIso U.1).hom_inv_id).symm
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change (j.appIso U.1).hom (ι.val.app (op (j ''ᵁ U.1)) s) = r
    rw [hs]
    exact congrArg (fun k : Γ(Z, U.1) ⟶ Γ(Z, U.1) => k r) (j.appIso U.1).inv_hom_id

lemma local_equation_on_chart (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (h : PresentsPullbackIdeal I f J ι)
    (U : Y.affineOpens) (V : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : CategoryTheory.Iso (C := U.1.toScheme.Modules)
      (J.sheaf.restrict U.1.ι) (structureSheaf U.1.toScheme)) :
    ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r} := by
  let : Mono ι := h.1
  let g : UnitEndomorphism.unit U.1.toScheme ⟶ UnitEndomorphism.unit U.1.toScheme :=
    e.inv ≫ restrictedInclusion J ι U.1.ι
  have : Mono g := mono_comp (C := U.1.toScheme.Modules) e.inv
    (restrictedInclusion J ι U.1.ι)
  refine ⟨UnitEndomorphism.equation g ⊤, UnitEndomorphism.equation_regular g ⊤, ?_⟩
  rw [← UnitEndomorphism.image_principal g ⊤,
    ← restricted_image_on_chart J ι h U.1.ι ⟨⊤, isAffineOpen_top _⟩ V
      (by simpa only [Scheme.Opens.ι_image_top] using hUV)]
  ext r
  change (∃ s, (restrictedInclusion J ι U.1.ι).val.app (op ⊤) s = r) ↔
    ∃ s, (restrictedInclusion J ι U.1.ι).val.app (op ⊤) (e.inv.val.app (op ⊤) s) = r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨e.hom.val.app (op ⊤) s, ?_⟩
    have ht : e.inv.val.app (op ⊤) (e.hom.val.app (op ⊤) s) = s := by
      exact congrArg (fun k : J.sheaf.restrict U.1.ι ⟶ J.sheaf.restrict U.1.ι =>
        k.val.app (op ⊤) s) e.hom_inv_id
    rw [ht]; exact hs
  · rintro ⟨s, hs⟩
    exact ⟨e.inv.val.app (op ⊤) s, hs⟩

lemma local_equations (hf : InvertiblePullbackIdeal I f) (y : Y) :
    ∃ U : Y.affineOpens, y ∈ U.1 ∧ ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r} := by
  obtain ⟨J, ι, h⟩ := hf
  obtain ⟨W, hyW, ⟨e⟩⟩ := J.locallyRankOne y
  obtain ⟨V, hV, hyV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f y ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ W ⊓ f ⁻¹ᵁ V from ⟨hyW, hyV⟩)
  refine ⟨⟨U, hU⟩, hyU, ?_⟩
  exact local_equation_on_chart J ι h ⟨U, hU⟩ ⟨V, hV⟩
    (hUV.trans inf_le_right) (frameOfLE J.sheaf (hUV.trans inf_le_left) e)

lemma invertible_iff_local_equations :
    InvertiblePullbackIdeal I f ↔
    ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧
      ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r} :=
  ⟨local_equations, invertible_of_local_equations⟩

lemma invertible_congr {X' : Scheme} {I' : X'.IdealSheafData} {f' : Y ⟶ X'}
    (he : I.comap f = I'.comap f') :
    InvertiblePullbackIdeal I f ↔ InvertiblePullbackIdeal I' f' := by
  rw [invertible_iff_local_equations, invertible_iff_local_equations, he]

end

noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X Y Z : Scheme}

lemma presents_restrict_general (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hf : PresentsPullbackIdeal I f J ι) (j : Z ⟶ Y) [IsOpenImmersion j] :
    PresentsPullbackIdeal I (j ≫ f) (restrictLineBundle J j) (restrictedInclusion J ι j) := by
  let : Mono ι := hf.1
  refine ⟨restrictedInclusion_mono J ι j, ?_⟩
  intro U V e
  change ((restrictedInclusion J ι j).val.app (Opposite.op U.1)).hom.range = _
  rw [restricted_image_on_chart J ι hf j U V ?_, ← Scheme.IdealSheafData.comap_comp]
  · exact IdealPullback.comap_ideal I (j ≫ f) U V e
  · rintro _ ⟨z, hz, rfl⟩
    exact e hz

lemma invertible_restrict_general (I : X.IdealSheafData) (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) (j : Z ⟶ Y) [IsOpenImmersion j] :
    InvertiblePullbackIdeal I (j ≫ f) := by
  obtain ⟨J, ι, h⟩ := hf
  exact ⟨restrictLineBundle J j, restrictedInclusion J ι j,
    presents_restrict_general I f J ι h j⟩

lemma invertible_of_cover (I : X.IdealSheafData) (f : Y ⟶ X) (C : Y.OpenCover)
    (hf : ∀ i, InvertiblePullbackIdeal I (C.f i ≫ f)) :
    InvertiblePullbackIdeal I f := by
  let J : LineBundle Y := {
    sheaf := IdealModule.closedModule (I.comap f)
    locallyRankOne y := by
      let i := C.idx y
      obtain ⟨z, hz⟩ := C.covers y
      obtain ⟨U, hzU, r, hr, hIr⟩ := local_equations (hf i) z
      let j := U.1.ι ≫ C.f i
      have he : ((I.comap f).comap j).ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩ =
          Ideal.span {r} := by
        simpa only [j, Scheme.IdealSheafData.comap_comp] using hIr
      obtain ⟨e⟩ := IdealModule.frame_restriction (I.comap f) j r he hr.1
      refine ⟨j.opensRange, ?_, ⟨IdealModule.frameOnRange _ j e⟩⟩
      exact ⟨⟨z, hzU⟩, hz⟩ }
  have : Mono (IdealModule.closedInclusion (I.comap f)) :=
    inferInstanceAs (Mono (IdealModule.inclusion (I.comap f).subschemeι))
  refine ⟨J, IdealModule.closedInclusion (I.comap f), this, ?_⟩
  intro U V e
  change ((IdealModule.closedInclusion (I.comap f)).val.app (Opposite.op U.1)).hom.range = _
  rw [IdealModule.closed_image]
  exact IdealPullback.comap_ideal I f U V e

end
end MaximalSeshadri.InvertibleLocal

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X B Y Z : Scheme} {I : X.IdealSheafData} {π : B ⟶ X}

lemma IsBlowup.hom_ext (hπ : IsBlowup I π) (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) {g h : Y ⟶ B}
    (hg : g ≫ π = f) (hh : h ≫ π = f) : g = h := by
  obtain ⟨l, _, hl⟩ := hπ.2 Y f hf
  exact (hl g hg).trans (hl h hh).symm

lemma IsBlowup.postIso (hπ : IsBlowup I π) (e : X ≅ Z)
    (J : Z.IdealSheafData) (he : J.comap e.hom = I) :
    IsBlowup J (π ≫ e.hom) := by
  have hcongr (W : Scheme) (f : W ⟶ X) :
      InvertiblePullbackIdeal J (f ≫ e.hom) ↔ InvertiblePullbackIdeal I f :=
    InvertibleLocal.invertible_congr (by rw [Scheme.IdealSheafData.comap_comp, he])
  refine ⟨(hcongr B π).mpr hπ.1, ?_⟩
  intro W f hf
  have hf' : InvertiblePullbackIdeal I (f ≫ e.inv) := by
    apply (hcongr W (f ≫ e.inv)).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hf
  obtain ⟨l, hl, huniq⟩ := hπ.2 W (f ≫ e.inv) hf'
  refine ⟨l, ?_, ?_⟩
  · change l ≫ π ≫ e.hom = f
    rw [← Category.assoc, hl, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro m hm
    apply huniq m
    rw [← cancel_mono e.hom, Category.assoc, hm, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]

lemma IsBlowup.open_baseChange (hπ : IsBlowup I π) (j : Z ⟶ X)
    [IsOpenImmersion j] :
    IsBlowup (I.comap j) (pullback.fst j π) := by
  have hcongr {W : Scheme} (g : W ⟶ Z) :
      InvertiblePullbackIdeal (I.comap j) g ↔ InvertiblePullbackIdeal I (g ≫ j) :=
    InvertibleLocal.invertible_congr (Scheme.IdealSheafData.comap_comp I g j).symm
  have hpic : InvertiblePullbackIdeal (I.comap j) (pullback.fst j π) := by
    apply (hcongr _).mpr
    rw [pullback.condition]
    exact InvertibleLocal.invertible_restrict_general I π hπ.1 (pullback.snd j π)
  refine ⟨hpic, ?_⟩
  intro W f hf
  obtain ⟨l, hl, huniq⟩ := hπ.2 W (f ≫ j) ((hcongr f).mp hf)
  refine ⟨pullback.lift f l hl.symm, pullback.lift_fst _ _ _, ?_⟩
  intro m hm
  apply pullback.hom_ext
  · simpa only [pullback.lift_fst] using hm
  · rw [pullback.lift_snd]
    apply huniq
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hm]

def IsBlowup.iso {B' : Scheme} {π' : B' ⟶ X} (hπ : IsBlowup I π)
    (hπ' : IsBlowup I π') : B ≅ B' where
  hom := (hπ'.2 B π hπ.1).choose
  inv := (hπ.2 B' π' hπ'.1).choose
  hom_inv_id := by
    apply hπ.hom_ext π hπ.1
    · rw [Category.assoc, (hπ.2 B' π' hπ'.1).choose_spec.1]
      exact (hπ'.2 B π hπ.1).choose_spec.1
    · simp
  inv_hom_id := by
    apply hπ'.hom_ext π' hπ'.1
    · rw [Category.assoc, (hπ'.2 B π hπ.1).choose_spec.1]
      exact (hπ.2 B' π' hπ'.1).choose_spec.1
    · simp

@[reassoc (attr := simp)]
lemma IsBlowup.iso_hom_comp {B' : Scheme} {π' : B' ⟶ X} (hπ : IsBlowup I π)
    (hπ' : IsBlowup I π') : (hπ.iso hπ').hom ≫ π' = π :=
  (hπ'.2 B π hπ.1).choose_spec.1

end

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X B B' Z : Scheme} {I : X.IdealSheafData} {π : B ⟶ X}

lemma IsBlowup.baseChangeSquare (hπ : IsBlowup I π) (j : Z ⟶ X)
    [IsOpenImmersion j] (ρ : B' ⟶ Z) (hρ : IsBlowup (I.comap j) ρ)
    (β : B' ⟶ B) (hβ : β ≫ π = ρ ≫ j) : IsPullback ρ β j π := by
  let e := hρ.iso (hπ.open_baseChange j)
  refine IsPullback.of_iso_pullback ⟨hβ.symm⟩ e
    (hρ.iso_hom_comp (hπ.open_baseChange j)) ?_
  apply hπ.hom_ext (ρ ≫ j)
  · exact (InvertibleLocal.invertible_congr
      (Scheme.IdealSheafData.comap_comp I ρ j)).mpr hρ.1
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      hρ.iso_hom_comp (hπ.open_baseChange j)]
  · exact hβ

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.IdealPullback
noncomputable section
open CategoryTheory AlgebraicGeometry
variable {X : Scheme.{0}} [IsAffine X]

lemma specIdeal_comap_toSpec (I : X.IdealSheafData) :
    (specIdeal (I.ideal ⟨⊤, isAffineOpen_top X⟩)).comap X.toSpecΓ = I := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [comap_top, specIdeal_top, Scheme.toSpecΓ_appTop, Ideal.map_map]
  change Ideal.map ((Scheme.ΓSpecIso Γ(X, ⊤)).hom.hom.comp
    (Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom) _ = _
  simp only [← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, Ideal.map_id]

lemma comap_isoSpec_inv (I : X.IdealSheafData) :
    I.comap X.isoSpec.inv = specIdeal (I.ideal ⟨⊤, isAffineOpen_top X⟩) := by
  conv_lhs => rw [← specIdeal_comap_toSpec I]
  rw [← Scheme.IdealSheafData.comap_comp]
  change (specIdeal _).comap (X.isoSpec.inv ≫ X.isoSpec.hom) = _
  rw [Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.AffineBlowup
noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X : Scheme.{0}} [IsAffine X] (I : X.IdealSheafData)

abbrev scheme : Scheme := ReesGrading.affineBlowup (I.ideal ⟨⊤, isAffineOpen_top X⟩)

def projection : scheme I ⟶ X :=
  ReesGrading.projection (I.ideal ⟨⊤, isAffineOpen_top X⟩) ≫ X.isoSpec.inv

theorem isBlowup : IsBlowup I (projection I) :=
  (rees_isBlowup (I.ideal ⟨⊤, isAffineOpen_top X⟩)).postIso X.isoSpec.symm I
    (IdealPullback.comap_isoSpec_inv I)

end
end MaximalSeshadri.AffineBlowup


end

end OAI
