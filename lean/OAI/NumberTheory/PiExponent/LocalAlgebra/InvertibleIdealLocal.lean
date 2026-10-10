import OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal
import OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension

namespace OAI

noncomputable section

namespace PiExponentSeshadri.UnitEndomorphism
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {X : Scheme.{u}}
abbrev unit (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf
variable (g : unit X ⟶ unit X)

def equation (U : X.Opens) : Γ(X, U) := g.val.app (op U) (1 : Γ(X, U))

lemma app_eq_mul (U : X.Opens) (a : Γ(X, U)) :
    g.val.app (op U) a = equation g U * a := by
  let F : Γ(X, U) →ₗ[Γ(X, U)] Γ(X, U) := (g.val.app (op U)).hom
  have h := F.map_smul a (1 : Γ(X, U))
  simpa only [smul_eq_mul, mul_one, mul_comm a, one_mul, F, equation] using! h

lemma image_principal (U : X.Opens) :
    (show Ideal Γ(X, U) from (g.val.app (op U)).hom.range) = Ideal.span {equation g U} := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact Ideal.mem_span_singleton.mpr ⟨b, app_eq_mul g U b⟩
  · intro ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
    exact ⟨b, (app_eq_mul g U b).trans hb.symm⟩

lemma equation_regular [Mono g] (U : X.Opens) : IsRegular (equation g U) := by
  let : Mono g.val := inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules X).map g))
  have hinj := PresheafOfModules.injective_of_mono g.val (op U)
  apply (Commute.isRegular_iff (fun a => Commute.all _ a)).mpr
  intro a b hab
  apply hinj
  simpa only [app_eq_mul] using! hab

end PiExponentSeshadri.UnitEndomorphism
namespace PiExponentSeshadri.InvertibleLocal

section
open CategoryTheory AlgebraicGeometry Opposite
open PiExponentSeshadri.Geometry
universe u
variable {X Y Z : Scheme} (I : X.IdealSheafData) (f : Y ⟶ X)
variable (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)

lemma image_eq_comap [IsAffine X] (h : PresentsPullbackIdeal I f J ι) (U : Y.affineOpens) :
    sectionImageIdeal J ι U.1 = (I.comap f).ideal U := by
  let V : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have e : U.1 ≤ f ⁻¹ᵁ V.1 := by simp [V]
  exact (h.2 U V e).trans (IdealPullback.comap_ideal I f U V e).symm

variable {I f}

private theorem mono_comp_iso {C : Type*} [Category C] {A B D : C}
    (g : A ⟶ B) (e : B ≅ D) [Mono g] : Mono (g ≫ e.hom) := inferInstance

private theorem mono_iso_inv_comp {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (g : A ⟶ D) [Mono g] : Mono (e.inv ≫ g) := inferInstance

def restrictedInclusion (j : Z ⟶ Y) [IsOpenImmersion j] :
    J.sheaf.restrict j ⟶ structureSheaf Z :=
  (Scheme.Modules.restrictFunctor j).map ι ≫ (Scheme.Modules.restrictUnitIso j).hom

instance restrictedInclusion_mono (j : Z ⟶ Y) [IsOpenImmersion j] [Mono ι] :
    Mono (restrictedInclusion J ι j) := by
  exact mono_comp_iso ((Scheme.Modules.restrictFunctor j).map ι)
    (Scheme.Modules.restrictUnitIso j)

lemma restricted_image [IsAffine X] (h : PresentsPullbackIdeal I f J ι)
    (j : Z ⟶ Y) [IsOpenImmersion j] (U : Z.affineOpens) :
    ((restrictedInclusion J ι j).val.app (op U.1)).hom.range =
      ((I.comap f).comap j).ideal U := by
  rw [(I.comap f).ideal_comap_of_isOpenImmersion j U]
  ext r
  change Γ(Z, U.1) at r
  change (∃ s, (restrictedInclusion J ι j).val.app (op U.1) s = r) ↔ _
  erw [Ideal.mem_comap, ← image_eq_comap I f J ι h
    ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩]
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
    (e : J.sheaf.restrict j ≅ structureSheaf Z) :
    ∃ r : Γ(Z, ⊤), IsRegular r ∧
      ((I.comap f).comap j).ideal ⟨⊤, isAffineOpen_top Z⟩ = Ideal.span {r} := by
  let : Mono ι := h.1
  let g : UnitEndomorphism.unit Z ⟶ UnitEndomorphism.unit Z :=
    e.inv ≫ restrictedInclusion J ι j
  let : Mono (restrictedInclusion J ι j) := restrictedInclusion_mono J ι j
  have : Mono g := mono_iso_inv_comp e (restrictedInclusion J ι j)
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

section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
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

open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
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

end PiExponentSeshadri.InvertibleLocal

end

end OAI
