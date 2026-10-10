import OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing
import OAI.NumberTheory.PiExponent.Approximation.SectionDivision
import OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct

namespace OAI

noncomputable section

namespace PiExponentSeshadri.InvertibleLocal
open CategoryTheory AlgebraicGeometry Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y Z : Scheme.{0}}

lemma frame_ideal [IsAffine X] {I : X.IdealSheafData} {f : Y ⟶ X}
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (h : PresentsPullbackIdeal I f J ι)
    (j : Z ⟶ Y) [IsOpenImmersion j] [IsAffine Z]
    (e : J.sheaf.restrict j ≅ O Z) :
    ((I.comap f).comap j).ideal ⟨⊤,isAffineOpen_top Z⟩ =
      Ideal.span {endValue (e.inv ≫ restrictedInclusion J ι j)} := by
  change _ = Ideal.span {UnitEndomorphism.equation (e.inv ≫ restrictedInclusion J ι j) ⊤}
  rw [← UnitEndomorphism.image_principal _ ⊤, ← restricted_image J ι h j ⟨⊤, isAffineOpen_top Z⟩]
  ext r
  change (∃ s, (restrictedInclusion J ι j).val.app (op ⊤) s = r) ↔
    ∃ s, (restrictedInclusion J ι j).val.app (op ⊤) (e.inv.val.app (op ⊤) s) = r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨e.hom.val.app (op ⊤) s, ?_⟩
    have ht : e.inv.val.app (op ⊤) (e.hom.val.app (op ⊤) s) = s :=
      congrArg (fun k : J.sheaf.restrict j ⟶ J.sheaf.restrict j => k.val.app (op ⊤) s) e.hom_inv_id
    rw [ht]; exact hs
  · rintro ⟨s, hs⟩
    exact ⟨e.inv.val.app (op ⊤) s, hs⟩
end PiExponentSeshadri.InvertibleLocal

namespace PiExponentSeshadri.ReesGrading
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SpecMaps

private theorem mono_inv_comp {D : Type*} [Category D] {A B C : D}
    (e : A ≅ B) (f : A ⟶ C) (hf : Mono f) : Mono (e.inv ≫ f) := by
  let := hf
  infer_instance

private theorem map_comp_through {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B T : C} {U V : D}
    (u : U ⟶ F.obj A) (s : A ⟶ B) (t : B ⟶ T) (v : F.obj T ⟶ V) :
    (u ≫ F.map s) ≫ F.map t ≫ v = (u ≫ F.map (s ≫ t)) ≫ v := by
  simp only [Functor.map_comp, Category.assoc]

variable {R : Type} [CommRing R] (I : Ideal R)
variable {B : Scheme.{0}} (f : B ⟶ Spec (.of R))
  (J : LineBundle B) (ι : J.sheaf ⟶ O B)
  (hJ : PresentsPullbackIdeal (IdealPullback.specIdeal I) f J ι)
include hJ

theorem relative_generator_section (a : I) :
    ∃ s : O B ⟶ J.sheaf,
      s ≫ ι = scalarEnd ((coordinate f) a.val) := by
  let : Mono ι := hJ.1
  obtain ⟨s,hs,-⟩ := global_division_of_local_lifts ι
      (scalarEnd ((coordinate f) a.val)) (by
    intro x
    obtain ⟨U,hx,⟨e⟩,-⟩ := common_affine_frames J J x
    let r := endValue (e.inv ≫ InvertibleLocal.restrictedInclusion J ι U.1.ι)
    have hI : I.map (coordinate (U.1.ι ≫ f)).hom = Ideal.span {r} := by
      rw [← IdealPullback.specIdeal_coordinate,Scheme.IdealSheafData.comap_comp]
      exact InvertibleLocal.frame_ideal J ι hJ U.1.ι e
    have hmem : coefficient (Scheme.Modules.restrictUnitIso U.1.ι)
        (restrictSection U.1.ι (scalarEnd ((coordinate f) a.val))) ∈ Ideal.span {r} := by
      rw [← hI]
      have he : coefficient (Scheme.Modules.restrictUnitIso U.1.ι)
          (restrictSection U.1.ι (scalarEnd ((coordinate f) a.val))) =
          coordinate (U.1.ι ≫ f) a.val := by
        erw [coefficient, endValue_restrict, endValue_scalarEnd]
        rw [coordinate_comp]
        rfl
      rw [he]
      exact Ideal.mem_map_of_mem _ a.property
    obtain ⟨t,ht⟩ := framed_local_division e (Scheme.Modules.restrictUnitIso U.1.ι)
      ((Scheme.Modules.restrictFunctor U.1.ι).map ι)
      (restrictSection U.1.ι (scalarEnd ((coordinate f) a.val))) hmem
    exact ⟨U.1,hx,t,ht⟩)
  exact ⟨s,hs⟩

theorem relative_generator_section_open (β : B ⟶ affineBlowup I) (hβ : β ≫ projection I = f) (a : I)
    (s : O B ⟶ J.sheaf)
    (hs : s ≫ ι = scalarEnd ((coordinate f) a.val)) :
    SectionOpens.isoOpen s = β ⁻¹ᵁ Proj.basicOpen (piece I) (generator I a) := by
  let : Mono ι := hJ.1
  ext x
  obtain ⟨U,hx,⟨e⟩,-⟩ := common_affine_frames J J x
  let g := e.inv ≫ InvertibleLocal.restrictedInclusion J ι U.1.ι
  have hg : Mono g := mono_inv_comp e (InvertibleLocal.restrictedInclusion J ι U.1.ι)
    (@InvertibleLocal.restrictedInclusion_mono _ _ J ι U.1.ι inferInstance hJ.1)
  let r := endValue g
  have hr : IsRegular r := @UnitEndomorphism.equation_regular U.1.toScheme g hg ⊤
  have hI : I.map (coordinate (U.1.ι ≫ f)).hom = Ideal.span {r} := by
    rw [← IdealPullback.specIdeal_coordinate,Scheme.IdealSheafData.comap_comp]
    exact InvertibleLocal.frame_ideal J ι hJ U.1.ι e
  let h := principalScheme I U.1.toScheme (coordinate (U.1.ι ≫ f)).hom r hI hr
  have hh : h = U.1.ι ≫ β := by
    apply invertible_unique I h (U.1.ι ≫ β) (U.1.ι ≫ f)
    · exact (principalScheme_projection I U.1.toScheme _ r hI hr).trans (factor _)
    · rw [Category.assoc,hβ]
    · exact InvertibleLocal.invertible_restrict _ _ ⟨J,ι,hJ⟩ U.1.ι
  have hscalar : coefficient e (restrictSection U.1.ι s) * r =
      coordinate (U.1.ι ≫ f) a.val := by
    have hcomp : (restrictSection U.1.ι s ≫ e.hom) ≫ g =
        restrictSection U.1.ι (scalarEnd ((coordinate f) a.val)) ≫
          (Scheme.Modules.restrictUnitIso U.1.ι).hom := by
      dsimp [g,InvertibleLocal.restrictedInclusion]
      simp only [Category.assoc,Iso.hom_inv_id_assoc]
      rw [← hs]
      simp only [restrictSection]
      exact map_comp_through (Scheme.Modules.restrictFunctor U.1.ι)
        (Scheme.Modules.restrictUnitIso U.1.ι).inv s ι
        (Scheme.Modules.restrictUnitIso U.1.ι).hom
    have H := congrArg (endValue (X := U.1.toScheme)) hcomp
    rw [coordinate_comp]
    exact ((endValue_comp (restrictSection U.1.ι s ≫ e.hom) g).symm.trans H).trans
      ((endValue_restrict U.1.ι (scalarEnd ((coordinate f) a.val))).trans
        (congrArg U.1.ι.appTop (endValue_scalarEnd ((coordinate f) a.val))))
  have hc : coefficient e (restrictSection U.1.ι s) =
      BlowupLift.coefficient I (coordinate (U.1.ι ≫ f)).hom r hI a := by
    apply hr.left
    exact (mul_comm _ _).trans (hscalar.trans
      (BlowupLift.mul_coefficient I _ r hI a).symm)
  have hloc : U.1.ι ⁻¹ᵁ SectionOpens.isoOpen s =
      U.1.ι ⁻¹ᵁ β ⁻¹ᵁ Proj.basicOpen (piece I) (generator I a) := by
    rw [preimage_isoOpen s U.1.ι e,hc]
    have H := principalScheme_preimage I U.1.toScheme _ r hI hr a
    change h ⁻¹ᵁ _ = _ at H
    rw [hh] at H
    exact H.symm
  exact SetLike.ext_iff.mp hloc ⟨x,hx⟩

end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SpecMaps
variable {R : Type} [CommRing R] (I : Ideal R)
variable {B : Scheme.{0}} (f : B ⟶ Spec (.of R))
  (J : LineBundle B) (ι : J.sheaf ⟶ O B)
  (hJ : PresentsPullbackIdeal (IdealPullback.specIdeal I) f J ι)
include hJ

theorem relative_affine_section_cover (hf : IsBlowup (IdealPullback.specIdeal I) f) :
    ∃ s : I → (O B ⟶ J.sheaf),
      (⨆ a, SectionOpens.isoOpen (s a)) = ⊤ ∧
      ∀ a, IsAffineOpen (SectionOpens.isoOpen (s a)) := by
  classical
  let e : B ≅ affineBlowup I := hf.iso (rees_isBlowup I)
  let : IsIso e.hom := ⟨⟨e.inv,e.hom_inv_id,e.inv_hom_id⟩⟩
  choose s hs using relative_generator_section I f J ι hJ
  have ho a := relative_generator_section_open I f J ι hJ e.hom
    (hf.iso_hom_comp (rees_isBlowup I)) a (s a) (hs a)
  refine ⟨s,?_,fun a => ?_⟩
  · simp only [ho]
    exact e.hom.iSup_preimage_eq_top (iSup_generator_basicOpen I)
  · rw [ho]
    exact @IsAffineOpen.preimage_of_isIso B (affineBlowup I) _
      (Proj.isAffineOpen_basicOpen (piece I) (generator I a) (generator_mem I a)
        (by decide : 0 < (1:ℕ))) e.hom e.isIso_hom
end PiExponentSeshadri.ReesGrading

end

end OAI
