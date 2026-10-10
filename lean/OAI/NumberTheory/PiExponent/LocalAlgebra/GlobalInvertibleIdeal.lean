import OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal

namespace OAI

namespace PiExponentSeshadri.InvertibleLocal
noncomputable section

section
open CategoryTheory AlgebraicGeometry Opposite
open PiExponentSeshadri.Geometry
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
  ext r
  change (∃ s, (restrictedInclusion J ι j).val.app (op U.1) s = r) ↔ _
  erw [Ideal.mem_comap, ← he]
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

private theorem mono_iso_inv_comp {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (g : A ⟶ D) [Mono g] : Mono (e.inv ≫ g) := inferInstance

lemma local_equation_on_chart (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (h : PresentsPullbackIdeal I f J ι)
    (U : Y.affineOpens) (V : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : J.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) :
    ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r} := by
  let : Mono ι := h.1
  let g : UnitEndomorphism.unit U.1.toScheme ⟶ UnitEndomorphism.unit U.1.toScheme :=
    e.inv ≫ restrictedInclusion J ι U.1.ι
  let : Mono (restrictedInclusion J ι U.1.ι) := restrictedInclusion_mono J ι U.1.ι
  have : Mono g := mono_iso_inv_comp e (restrictedInclusion J ι U.1.ι)
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

open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
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
end PiExponentSeshadri.InvertibleLocal

end OAI
