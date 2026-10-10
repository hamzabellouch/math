import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Blowup.LocalUniversal
import OAI.AlgebraicGeometry.Seshadri.Blowup.ReesSections

namespace OAI


                                              
section

namespace MaximalSeshadri.ReesGrading
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Frames MaximalSeshadri.SpecMaps

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
        change endValue (restrictSection U.1.ι
          (scalarEnd ((coordinate f) a.val)) ≫
          (Scheme.Modules.restrictUnitIso U.1.ι).hom) = _
        rw [endValue_restrict, endValue_scalarEnd,coordinate_comp]
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
  have : Mono (C := B.Modules) (X := J.sheaf) (Y := structureSheaf B) ι := hJ.1
  ext x
  obtain ⟨U,hx,⟨e⟩,-⟩ := common_affine_frames J J x
  let g : UnitEndomorphism.unit U.1.toScheme ⟶
      UnitEndomorphism.unit U.1.toScheme :=
    e.inv ≫ InvertibleLocal.restrictedInclusion J ι U.1.ι
  have : Mono (InvertibleLocal.restrictedInclusion J ι U.1.ι) :=
    InvertibleLocal.restrictedInclusion_mono J ι U.1.ι
  have : Mono g := mono_comp (C := U.1.toScheme.Modules) e.inv
    (InvertibleLocal.restrictedInclusion J ι U.1.ι)
  let r := endValue g
  have hr : IsRegular r := UnitEndomorphism.equation_regular g ⊤
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
      change (restrictSection U.1.ι s ≫ e.hom) ≫
        (e.inv ≫ InvertibleLocal.restrictedInclusion J ι U.1.ι) = _
      rw [Category.assoc, e.hom_inv_id_assoc]
      rw [← hs]
      change ((Scheme.Modules.restrictUnitIso U.1.ι).inv ≫
        (Scheme.Modules.restrictFunctor U.1.ι).map s) ≫
        ((Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
          (Scheme.Modules.restrictUnitIso U.1.ι).hom) =
        ((Scheme.Modules.restrictUnitIso U.1.ι).inv ≫
          (Scheme.Modules.restrictFunctor U.1.ι).map (s ≫ ι)) ≫
          (Scheme.Modules.restrictUnitIso U.1.ι).hom
      calc
        _ = ((Scheme.Modules.restrictUnitIso U.1.ι).inv ≫
            ((Scheme.Modules.restrictFunctor U.1.ι).map s ≫
              (Scheme.Modules.restrictFunctor U.1.ι).map ι)) ≫
            (Scheme.Modules.restrictUnitIso U.1.ι).hom :=
          (Category.assoc (obj := U.1.toScheme.Modules)
            ((Scheme.Modules.restrictUnitIso U.1.ι).inv ≫
              (Scheme.Modules.restrictFunctor U.1.ι).map s)
            ((Scheme.Modules.restrictFunctor U.1.ι).map ι)
            (Scheme.Modules.restrictUnitIso U.1.ι).hom).symm.trans
          (congrArg (fun sectionMap => sectionMap ≫
            (Scheme.Modules.restrictUnitIso U.1.ι).hom)
            (Category.assoc (obj := U.1.toScheme.Modules)
              (Scheme.Modules.restrictUnitIso U.1.ι).inv
              ((Scheme.Modules.restrictFunctor U.1.ι).map s)
              ((Scheme.Modules.restrictFunctor U.1.ι).map ι)))
        _ = _ := congrArg (fun sectionMap =>
          ((Scheme.Modules.restrictUnitIso U.1.ι).inv ≫ sectionMap) ≫
            (Scheme.Modules.restrictUnitIso U.1.ι).hom)
          ((Scheme.Modules.restrictFunctor U.1.ι).map_comp s ι).symm
    calc
      coefficient e (restrictSection U.1.ι s) * r =
          endValue ((restrictSection U.1.ι s ≫ e.hom) ≫ g) :=
        (endValue_comp (restrictSection U.1.ι s ≫ e.hom) g).symm
      _ = endValue (restrictSection U.1.ι
          (scalarEnd ((coordinate f) a.val)) ≫
          (Scheme.Modules.restrictUnitIso U.1.ι).hom) := congrArg endValue hcomp
      _ = _ := by
        rw [endValue_restrict, endValue_scalarEnd, coordinate_comp]
        rfl
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
end MaximalSeshadri.ReesGrading

namespace MaximalSeshadri.ReesGrading
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Frames MaximalSeshadri.SpecMaps
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
  let e : B ≅ Proj (piece I) := hf.iso (rees_isBlowup I)
  choose s hs using relative_generator_section I f J ι hJ
  have ho a := relative_generator_section_open I f J ι hJ e.hom
    (hf.iso_hom_comp (rees_isBlowup I)) a (s a) (hs a)
  refine ⟨s,?_,fun a => ?_⟩
  · simp only [ho]
    exact e.hom.iSup_preimage_eq_top (iSup_generator_basicOpen I)
  · rw [ho]
    exact (Proj.isAffineOpen_basicOpen (piece I) (generator I a) (generator_mem I a)
      (by decide : 0 < (1:ℕ))).preimage_of_isIso e.hom
end
end MaximalSeshadri.ReesGrading

end

end OAI
