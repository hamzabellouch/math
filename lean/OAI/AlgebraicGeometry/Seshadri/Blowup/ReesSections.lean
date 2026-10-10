import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorDivision
import OAI.AlgebraicGeometry.Seshadri.Blowup.LocalEquations

namespace OAI


                                      
section

namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

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
end
end MaximalSeshadri.InvertibleLocal

namespace MaximalSeshadri.ReesGrading
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Frames MaximalSeshadri.SpecMaps

variable {R : Type} [CommRing R] (I : Ideal R)

theorem generator_section (a : I) :
    ∃ s : O (affineBlowup I) ⟶ (exceptionalLineBundle I).sheaf,
      s ≫ exceptionalInclusion I = scalarEnd ((coordinate (projection I)) a.val) := by
  let J := exceptionalLineBundle I
  let ι := exceptionalInclusion I
  have hJ := exceptional_presents I
  have : Mono ι := hJ.1
  obtain ⟨s,hs,-⟩ := global_division_of_local_lifts ι
      (scalarEnd ((coordinate (projection I)) a.val)) (by
    intro x
    obtain ⟨U,hx,⟨e⟩,-⟩ := common_affine_frames J J x
    let r := endValue (e.inv ≫ InvertibleLocal.restrictedInclusion J ι U.1.ι)
    have hI : I.map (coordinate (U.1.ι ≫ projection I)).hom = Ideal.span {r} := by
      rw [← IdealPullback.specIdeal_coordinate,Scheme.IdealSheafData.comap_comp]
      exact InvertibleLocal.frame_ideal J ι hJ U.1.ι e
    have hmem : coefficient (Scheme.Modules.restrictUnitIso U.1.ι)
        (restrictSection U.1.ι (scalarEnd ((coordinate (projection I)) a.val))) ∈ Ideal.span {r} := by
      rw [← hI]
      have he : coefficient (Scheme.Modules.restrictUnitIso U.1.ι)
          (restrictSection U.1.ι (scalarEnd ((coordinate (projection I)) a.val))) =
          coordinate (U.1.ι ≫ projection I) a.val := by
        change endValue (restrictSection U.1.ι
          (scalarEnd ((coordinate (projection I)) a.val)) ≫
          (Scheme.Modules.restrictUnitIso U.1.ι).hom) = _
        rw [endValue_restrict, endValue_scalarEnd,coordinate_comp]
        rfl
      rw [he]
      exact Ideal.mem_map_of_mem _ a.property
    obtain ⟨t,ht⟩ := framed_local_division e (Scheme.Modules.restrictUnitIso U.1.ι)
      ((Scheme.Modules.restrictFunctor U.1.ι).map ι)
      (restrictSection U.1.ι (scalarEnd ((coordinate (projection I)) a.val))) hmem
    exact ⟨U.1,hx,t,ht⟩)
  exact ⟨s,hs⟩

theorem generator_section_open (a : I)
    (s : O (affineBlowup I) ⟶ (exceptionalLineBundle I).sheaf)
    (hs : s ≫ exceptionalInclusion I = scalarEnd ((coordinate (projection I)) a.val)) :
    SectionOpens.isoOpen s = Proj.basicOpen (piece I) (generator I a) := by
  let J := exceptionalLineBundle I
  let ι : J.sheaf ⟶ structureSheaf (affineBlowup I) := exceptionalInclusion I
  have hJ := exceptional_presents I
  have : Mono ι := hJ.1
  ext x
  obtain ⟨U,hx,⟨e⟩,-⟩ := common_affine_frames J J x
  let g : UnitEndomorphism.unit U.1.toScheme ⟶ UnitEndomorphism.unit U.1.toScheme :=
    e.inv ≫ InvertibleLocal.restrictedInclusion J ι U.1.ι
  have : Mono g := mono_comp (C := U.1.toScheme.Modules) e.inv
    (InvertibleLocal.restrictedInclusion J ι U.1.ι)
  let r := endValue g
  have hr : IsRegular r := UnitEndomorphism.equation_regular g ⊤
  have hI : I.map (coordinate (U.1.ι ≫ projection I)).hom = Ideal.span {r} := by
    rw [← IdealPullback.specIdeal_coordinate,Scheme.IdealSheafData.comap_comp]
    exact InvertibleLocal.frame_ideal J ι hJ U.1.ι e
  let h := principalScheme I U.1.toScheme (coordinate (U.1.ι ≫ projection I)).hom r hI hr
  have hh : h = U.1.ι := by
    apply invertible_unique I h U.1.ι (U.1.ι ≫ projection I)
    · exact (principalScheme_projection I U.1.toScheme _ r hI hr).trans (factor _)
    · rfl
    · exact InvertibleLocal.invertible_restrict _ _ (exceptional_invertible I) U.1.ι
  have hscalar : coefficient e (restrictSection U.1.ι s) * r =
      coordinate (U.1.ι ≫ projection I) a.val := by
    have hcomp : (restrictSection U.1.ι s ≫ e.hom) ≫ g =
        restrictSection U.1.ι (scalarEnd ((coordinate (projection I)) a.val)) ≫
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
          (scalarEnd ((coordinate (projection I)) a.val)) ≫
          (Scheme.Modules.restrictUnitIso U.1.ι).hom) := congrArg endValue hcomp
      _ = _ := by
        rw [endValue_restrict, endValue_scalarEnd, coordinate_comp]
        rfl
  have hc : coefficient e (restrictSection U.1.ι s) =
      BlowupLift.coefficient I (coordinate (U.1.ι ≫ projection I)).hom r hI a := by
    apply hr.left
    exact (mul_comm _ _).trans (hscalar.trans
      (BlowupLift.mul_coefficient I _ r hI a).symm)
  have hloc : U.1.ι ⁻¹ᵁ SectionOpens.isoOpen s =
      U.1.ι ⁻¹ᵁ Proj.basicOpen (piece I) (generator I a) := by
    rw [preimage_isoOpen s U.1.ι e,hc]
    have H := principalScheme_preimage I U.1.toScheme _ r hI hr a
    change h ⁻¹ᵁ _ = _ at H
    rw [hh] at H
    exact H.symm
  exact SetLike.ext_iff.mp hloc ⟨x,hx⟩

theorem exceptional_affine_section_cover :
    ∃ s : I → (O (affineBlowup I) ⟶ (exceptionalLineBundle I).sheaf),
      (⨆ a, SectionOpens.isoOpen (s a)) = ⊤ ∧
      ∀ a, IsAffineOpen (SectionOpens.isoOpen (s a)) := by
  classical
  choose s hs using generator_section I
  have ho a := generator_section_open I a (s a) (hs a)
  refine ⟨s,?_,fun a => ?_⟩
  · simp only [ho]
    exact iSup_generator_basicOpen I
  · rw [ho]
    exact Proj.isAffineOpen_basicOpen (piece I) (generator I a) (generator_mem I a)
      (by decide : 0 < (1:ℕ))
end
end MaximalSeshadri.ReesGrading

end

end OAI
