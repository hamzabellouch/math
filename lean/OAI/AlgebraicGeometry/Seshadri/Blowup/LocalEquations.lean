import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.PowerExtension
import OAI.AlgebraicGeometry.Seshadri.Blowup.Uniqueness

namespace OAI

section
namespace MaximalSeshadri.UnitEndomorphism
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {X : Scheme.{u}}
def unit (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf
variable (g : unit X ⟶ unit X)

def equation (U : X.Opens) : Γ(X, U) := g.val.app (op U) (1 : Γ(X, U))

lemma app_eq_mul (U : X.Opens) (a : Γ(X, U)) :
    g.val.app (op U) a = equation g U * a := by
  let sectionMap : Γ(X, U) →ₗ[Γ(X, U)] Γ(X, U) := (g.val.app (op U)).hom
  change sectionMap a = sectionMap 1 * a
  simpa only [smul_eq_mul, mul_one, mul_comm a, one_mul] using sectionMap.map_smul a 1

lemma image_principal (U : X.Opens) :
    (show Ideal Γ(X, U) from (g.val.app (op U)).hom.range) = Ideal.span {equation g U} := by
  ext a
  change (∃ b : Γ(X, U), g.val.app (op U) b = a) ↔ _
  constructor
  · rintro ⟨b, hb⟩
    exact Ideal.mem_span_singleton.mpr ⟨b, hb.symm.trans (app_eq_mul g U b)⟩
  · intro ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
    exact ⟨b, (app_eq_mul g U b).trans hb.symm⟩

lemma equation_regular [Mono g] (U : X.Opens) : IsRegular (equation g U) := by
  let : Mono g.val := inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules X).map g))
  have hinj := PresheafOfModules.injective_of_mono g.val (op U)
  apply (Commute.isRegular_iff (fun a => Commute.all _ a)).mpr
  intro a b hab
  apply hinj
  exact (app_eq_mul g U a).trans (hab.trans (app_eq_mul g U b).symm)

end
end MaximalSeshadri.UnitEndomorphism
namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open MaximalSeshadri.Geometry
universe u
variable {X Y Z : Scheme} (I : X.IdealSheafData) (f : Y ⟶ X)
variable (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)

lemma image_eq_comap [IsAffine X] (h : PresentsPullbackIdeal I f J ι) (U : Y.affineOpens) :
    sectionImageIdeal J ι U.1 = (I.comap f).ideal U := by
  let V : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have e : U.1 ≤ f ⁻¹ᵁ V.1 := by simp [V]
  exact (h.2 U V e).trans (IdealPullback.comap_ideal I f U V e).symm

variable {I f}

def restrictedInclusion (j : Z ⟶ Y) [IsOpenImmersion j] :
    J.sheaf.restrict j ⟶ structureSheaf Z :=
  (Scheme.Modules.restrictFunctor j).map ι ≫ (Scheme.Modules.restrictUnitIso j).hom

instance restrictedInclusion_mono (j : Z ⟶ Y) [IsOpenImmersion j] [Mono ι] :
    Mono (restrictedInclusion J ι j) := by
  have : Mono (C := Z.Modules) ((Scheme.Modules.restrictFunctor j).map ι) := by
    apply (Scheme.Modules.toPresheafOfModules Z).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro U
    let : Mono ι.val :=
      inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules Y).map ι))
    exact PresheafOfModules.injective_of_mono ι.val (op (j ''ᵁ U.unop))
  let unitIso : (Scheme.Modules.restrictFunctor j).obj (structureSheaf Y) ≅
      structureSheaf Z := Scheme.Modules.restrictUnitIso j
  exact mono_comp (C := Z.Modules) ((Scheme.Modules.restrictFunctor j).map ι) unitIso.hom

lemma restricted_image [IsAffine X] (h : PresentsPullbackIdeal I f J ι)
    (j : Z ⟶ Y) [IsOpenImmersion j] (U : Z.affineOpens) :
    ((restrictedInclusion J ι j).val.app (op U.1)).hom.range =
      ((I.comap f).comap j).ideal U := by
  rw [(I.comap f).ideal_comap_of_isOpenImmersion j U]
  apply Ideal.ext
  intro (r : Γ(Z, U.1))
  change (∃ s, (restrictedInclusion J ι j).val.app (op U.1) s = r) ↔
    (j.appIso U.1).inv r ∈ (I.comap f).ideal
      ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩
  refine Iff.trans ?_ (SetLike.ext_iff.mp (image_eq_comap I f J ι h
    ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩) _)
  change (∃ s, _) ↔ ∃ s, ι.val.app (op (j ''ᵁ U.1)) s = (j.appIso U.1).inv r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change (j.appIso U.1).hom (ι.val.app (op (j ''ᵁ U.1)) s) = r at hs
    rw [← hs]
    exact (congrArg (fun k : Γ(Y, j ''ᵁ U.1) ⟶ Γ(Y, j ''ᵁ U.1) => k (ι.val.app (op (j ''ᵁ U.1)) s))
      (j.appIso U.1).hom_inv_id).symm
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change (j.appIso U.1).hom (ι.val.app (op (j ''ᵁ U.1)) s) = r
    rw [hs]
    exact congrArg (fun k : Γ(Z, U.1) ⟶ Γ(Z, U.1) => k r) (j.appIso U.1).inv_hom_id

lemma local_equation [IsAffine X] (h : PresentsPullbackIdeal I f J ι)
    (j : Z ⟶ Y) [IsOpenImmersion j] [IsAffine Z]
    (e : CategoryTheory.Iso (C := Z.Modules) (J.sheaf.restrict j) (structureSheaf Z)) :
    ∃ r : Γ(Z, ⊤), IsRegular r ∧
      ((I.comap f).comap j).ideal ⟨⊤, isAffineOpen_top Z⟩ = Ideal.span {r} := by
  let : Mono ι := h.1
  let g : UnitEndomorphism.unit Z ⟶ UnitEndomorphism.unit Z :=
    e.inv ≫ restrictedInclusion J ι j
  have : Mono g := mono_comp (C := Z.Modules) e.inv (restrictedInclusion J ι j)
  refine ⟨UnitEndomorphism.equation g ⊤, UnitEndomorphism.equation_regular g ⊤, ?_⟩
  rw [← UnitEndomorphism.image_principal g ⊤, ← restricted_image J ι h j ⟨⊤, isAffineOpen_top Z⟩]
  ext r
  change (∃ s, (restrictedInclusion J ι j).val.app (op ⊤) s = r) ↔
    ∃ s, (restrictedInclusion J ι j).val.app (op ⊤) (e.inv.val.app (op ⊤) s) = r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨e.hom.val.app (op ⊤) s, ?_⟩
    have ht : e.inv.val.app (op ⊤) (e.hom.val.app (op ⊤) s) = s := by
      exact congrArg (fun k : J.sheaf.restrict j ⟶ J.sheaf.restrict j => k.val.app (op ⊤) s)
        e.hom_inv_id
    rw [ht]; exact hs
  · rintro ⟨s, hs⟩
    exact ⟨e.inv.val.app (op ⊤) s, hs⟩

end

noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X Y : Scheme}

lemma affine_local_equation [IsAffine X] (I : X.IdealSheafData) (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) (y : Y) :
    ∃ U : Y.affineOpens, y ∈ U.1 ∧ ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩ =
        Ideal.span {r} := by
  obtain ⟨J, ι, h⟩ := hf
  obtain ⟨U, hyU, ⟨e⟩⟩ := affine_frame J y
  refine ⟨U, hyU, ?_⟩
  exact local_equation J ι h U.1.ι e

end

noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X Y Z : Scheme}

def restrictLineBundle (J : LineBundle Y) (j : Z ⟶ Y) [IsOpenImmersion j] : LineBundle Z where
  sheaf := J.sheaf.restrict j
  locallyRankOne z := by
    obtain ⟨U, hzU, ⟨e⟩⟩ := J.locallyRankOne (j z)
    let V := j ⁻¹ᵁ U
    refine ⟨V, hzU, ⟨?_⟩⟩
    let e' := (Scheme.Modules.restrictFunctorComp (j ∣_ U) U.ι).app J.sheaf ≪≫
      (Scheme.Modules.restrictFunctor (j ∣_ U)).mapIso e ≪≫
      Scheme.Modules.restrictUnitIso (j ∣_ U)
    have e'' : J.sheaf.restrict (V.ι ≫ j) ≅ structureSheaf V.toScheme := by
      simp only [morphismRestrict_ι] at e'
      exact e'
    exact ((Scheme.Modules.restrictFunctorComp V.ι j).app J.sheaf).symm ≪≫ e''

lemma presents_restrict [IsAffine X] (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hf : PresentsPullbackIdeal I f J ι) (j : Z ⟶ Y) [IsOpenImmersion j] :
    PresentsPullbackIdeal I (j ≫ f) (restrictLineBundle J j) (restrictedInclusion J ι j) := by
  let : Mono ι := hf.1
  refine ⟨restrictedInclusion_mono J ι j, ?_⟩
  intro U V e
  change ((restrictedInclusion J ι j).val.app (Opposite.op U.1)).hom.range = _
  rw [restricted_image J ι hf j U, ← Scheme.IdealSheafData.comap_comp]
  exact IdealPullback.comap_ideal I (j ≫ f) U V e

lemma invertible_restrict [IsAffine X] (I : X.IdealSheafData) (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) (j : Z ⟶ Y) [IsOpenImmersion j] :
    InvertiblePullbackIdeal I (j ≫ f) := by
  obtain ⟨J, ι, h⟩ := hf
  exact ⟨restrictLineBundle J j, restrictedInclusion J ι j, presents_restrict I f J ι h j⟩

end
end MaximalSeshadri.InvertibleLocal

namespace MaximalSeshadri.IdealPullback
noncomputable section
open CategoryTheory AlgebraicGeometry
variable {R : Type} [CommRing R] (I : Ideal R)

lemma specIdeal_coordinate {Y : Scheme} [IsAffine Y]
    (f : Y ⟶ Spec (CommRingCat.of R)) :
    ((specIdeal I).comap f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      I.map (SpecMaps.coordinate f).hom := by
  rw [comap_top, specIdeal_top, Ideal.map_map]
  rfl

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.ReesGrading
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Geometry
open SpecMaps
variable {R : Type} [CommRing R] (I : Ideal R)

lemma invertible_unique {Y : Scheme} (g h : Y ⟶ affineBlowup I)
    (f : Y ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ projection I = f) (hh : h ≫ projection I = f)
    (hf : InvertiblePullbackIdeal (IdealPullback.specIdeal I) f) : g = h := by
  apply Scheme.hom_ext_of_forall g h
  intro y
  obtain ⟨U, hyU, r, hr, hIr⟩ :=
    InvertibleLocal.affine_local_equation (IdealPullback.specIdeal I) f hf y
  refine ⟨U.1, hyU, ?_⟩
  apply principal_unique I (U.1.ι ≫ g) (U.1.ι ≫ h) (U.1.ι ≫ f)
    (by rw [Category.assoc, hg]) (by rw [Category.assoc, hh]) r _ hr
  rwa [← Scheme.IdealSheafData.comap_comp, IdealPullback.specIdeal_coordinate] at hIr

lemma local_lift {Y : Scheme} (f : Y ⟶ Spec (CommRingCat.of R))
    (hf : InvertiblePullbackIdeal (IdealPullback.specIdeal I) f) (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ ∃ h : U.toScheme ⟶ affineBlowup I,
      h ≫ projection I = U.ι ≫ f := by
  obtain ⟨U, hyU, r, hr, hIr⟩ :=
    InvertibleLocal.affine_local_equation (IdealPullback.specIdeal I) f hf y
  rw [← Scheme.IdealSheafData.comap_comp, IdealPullback.specIdeal_coordinate] at hIr
  refine ⟨U.1, hyU, principalScheme I U.1.toScheme (coordinate (U.1.ι ≫ f)).hom r hIr hr, ?_⟩
  rw [principalScheme_projection]
  exact factor (U.1.ι ≫ f)

theorem affineBlowup_universal {Y : Scheme} (f : Y ⟶ Spec (CommRingCat.of R))
    (hf : InvertiblePullbackIdeal (IdealPullback.specIdeal I) f) :
    ∃! h : Y ⟶ affineBlowup I, h ≫ projection I = f := by
  classical
  choose U hyU g hg using local_lift I f hf
  let C : Y.OpenCover := {
    I₀ := Y
    X y := (U y).toScheme
    f y := (U y).ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun y => ⟨y, ?_⟩, inferInstance⟩
      simpa using hyU y }
  have hcompat (x y : C.I₀) : pullback.fst (C.f x) (C.f y) ≫ g x =
      pullback.snd (C.f x) (C.f y) ≫ g y := by
    let j := pullback.fst (C.f x) (C.f y) ≫ C.f x
    apply invertible_unique I _ _ (j ≫ f)
    · rw [Category.assoc, hg x]
      rfl
    · rw [Category.assoc, hg y]
      exact (pullback.condition_assoc f).symm
    · exact InvertibleLocal.invertible_restrict (IdealPullback.specIdeal I) f hf j
  refine ⟨C.glueMorphisms g hcompat, ?_, ?_⟩
  · apply C.hom_ext
    intro y
    rw [← Category.assoc, C.ι_glueMorphisms]
    exact hg y
  · intro h hh
    exact invertible_unique I h _ f hh (by
      apply C.hom_ext
      intro y
      rw [← Category.assoc, C.ι_glueMorphisms]
      exact hg y) hf

end
end MaximalSeshadri.ReesGrading

end

end OAI
