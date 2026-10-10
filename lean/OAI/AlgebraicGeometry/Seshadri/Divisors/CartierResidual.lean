import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorInclusion
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.IdealEquation
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionCoefficientOrder

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini

variable {X Y : Scheme.{0}}

lemma pullback_zero_coefficient_mem_closed (_p : X ⟶ Spec (CommRingCat.of ℂ))
    (f : Y ⟶ X) [IsClosedImmersion f] (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (hs : pullbackSection f s = 0) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    affineCoefficient U e s ∈ f.ker.ideal U := by
  rw [Scheme.Hom.ker_apply]
  change f.app U.1 (affineCoefficient U e s) = 0
  obtain ⟨eF,he⟩ := exists_restricted_pullback_frame f U.1 e s
  have hzero : coefficient eF
      (restrictSection (f ⁻¹ᵁ U.1).ι (pullbackSection f s)) = 0 := by
    rw [hs,restrictSection_zero,coefficient_zero]
  rw [he] at hzero
  apply ((ConcreteCategory.bijective_of_isIso (f ⁻¹ᵁ U.1).topIso.inv).injective)
  rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appTop,
    Scheme.Hom.resLE_app_top] at hzero
  simpa only [affineCoefficient, Scheme.Hom.appLE_eq_app, CommRingCat.comp_apply,
    map_zero] using hzero

theorem IntegralCurve.divide_section (S : Surface) (C : IntegralCurve S)
    (J M : LineBundle S.scheme) (ι : J.sheaf ⟶ O S.scheme)
    (hJ : PresentsPullbackIdeal C.embedding.ker (𝟙 S.scheme) J ι)
    (s : O S.scheme ⟶ M.sheaf) (hs : pullbackSection C.embedding s = 0) :
    ∃! q : O S.scheme ⟶ (J.tensor M).sheaf, q ≫ tensorInclusion J M ι = s := by
  let : Mono (C := S.scheme.Modules) (tensorInclusion J M ι) :=
    @tensorInclusion_mono S.scheme J M ι hJ.1
  apply global_division_of_local_lifts
  intro x
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames J M x
  refine ⟨U.1,hx,?_⟩
  apply framed_local_division (tensorFrame J M U.1 e f) f
  have hm := pullback_zero_coefficient_mem_closed S.structureMap C.embedding M s hs U f
  rw [InvertibleLocal.presented_frame_equation C.embedding.ker J ι hJ U e,
    ← tensor_inclusion_ideal J M ι U e f,Ideal.mem_span_singleton] at hm
  obtain ⟨a,ha⟩ := hm
  rw [Ideal.mem_span_singleton]
  refine ⟨U.1.topIso.inv a,?_⟩
  have H := congrArg (fun sectionValue => U.1.topIso.inv sectionValue) ha
  simpa only [affineCoefficient,map_mul,U.1.topIso.hom_inv_id_apply] using H

lemma affineCoefficient_tensorInclusion (J M : LineBundle X) (ι : J.sheaf ⟶ O X)
    (U : X.affineOpens) (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (f : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (q : O X ⟶ (J.tensor M).sheaf) :
    Associated
      (U.1.topIso.hom (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
        (Scheme.Modules.restrictUnitIso U.1.ι).hom)) *
        affineCoefficient U (tensorFrame J M U.1 e f) q)
      (affineCoefficient U f (q ≫ tensorInclusion J M ι)) := by
  unfold affineCoefficient
  have hvalue : endValue ((tensorFrame J M U.1 e f).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (tensorInclusion J M ι) ≫ f.hom) =
      endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
        (Scheme.Modules.restrictUnitIso U.1.ι).hom) *
        endValue (tensorUnitTwist M U.1 f).inv :=
    (congrArg (endValue (X := U.1.toScheme))
      (tensor_inclusion_framed J M ι U.1 e f)).trans
        (endValue_comp _ _)
  rw [show restrictSection U.1.ι (q ≫ tensorInclusion J M ι) =
    restrictSection U.1.ι q ≫ (Scheme.Modules.restrictFunctor U.1.ι).map
      (tensorInclusion J M ι) by
        exact (congrArg (fun morphism => (Scheme.Modules.restrictUnitIso U.1.ι).inv ≫
          morphism) ((Scheme.Modules.restrictFunctor U.1.ι).map_comp q
            (tensorInclusion J M ι))).trans (Category.assoc _ _ _).symm]
  rw [coefficient_postcompose (tensorFrame J M U.1 e f) f,
    hvalue, map_mul, map_mul]
  have hu : IsUnit (U.1.topIso.hom (endValue (tensorUnitTwist M U.1 f).inv)) :=
    ((end_isIso_iff _).mp (inferInstance : IsIso (tensorUnitTwist M U.1 f).inv)).map
      U.1.topIso.hom.hom
  rw [show U.1.topIso.hom (coefficient (tensorFrame J M U.1 e f) (restrictSection U.1.ι q)) *
    (U.1.topIso.hom (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
      (Scheme.Modules.restrictUnitIso U.1.ι).hom)) *
      U.1.topIso.hom (endValue (tensorUnitTwist M U.1 f).inv)) =
    (U.1.topIso.hom (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
      (Scheme.Modules.restrictUnitIso U.1.ι).hom)) *
      U.1.topIso.hom (coefficient (tensorFrame J M U.1 e f) (restrictSection U.1.ι q))) *
      U.1.topIso.hom (endValue (tensorUnitTwist M U.1 f).inv) by ring]
  simpa only [mul_one] using (associated_one_iff_isUnit.mpr hu).symm.mul_left
    (U.1.topIso.hom (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
      (Scheme.Modules.restrictUnitIso U.1.ι).hom)) *
      U.1.topIso.hom (coefficient (tensorFrame J M U.1 e f) (restrictSection U.1.ι q)))

end
end MaximalSeshadri.Geometry

end

end OAI
