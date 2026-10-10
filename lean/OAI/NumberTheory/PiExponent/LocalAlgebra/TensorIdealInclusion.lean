import OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation
import OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers
import OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

def tensorUnitTwist (M : LineBundle X) (U : X.Opens)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) : O U.toScheme ≅ O U.toScheme :=
  f.symm ≪≫ (Scheme.Modules.restrictFunctor U.ι).mapIso (moduleTensorUnit M.sheaf).symm ≪≫
    moduleTensorRestrict U (O X) M.sheaf ≪≫
      moduleTensorIso (Scheme.Modules.restrictUnitIso U.ι) f ≪≫ moduleTensorUnit (O U.toScheme)

lemma moduleTensorIso_inv {M N P Q : X.Modules} (e : M ≅ N) (f : P ≅ Q) :
    (moduleTensorIso e f).inv = moduleTensorMap e.inv f.inv := rfl

def tensorInclusion (J M : LineBundle X) (ι : J.sheaf ⟶ O X) :
    (J.tensor M).sheaf ⟶ M.sheaf :=
  moduleTensorMap ι (𝟙 M.sheaf) ≫ (moduleTensorUnit M.sheaf).hom

private lemma frame_square {C : Type*} [Category C]
    {A B A' B' T O : C} (r : A ≅ A') (r' : B ≅ B')
    (e : A' ≅ T) (e' : B' ≅ T) (u : T ≅ O)
    (m : A ⟶ B) (p : A' ⟶ B') (a : O ⟶ O)
    (hn : m ≫ r'.hom = r.hom ≫ p)
    (hs : e.inv ≫ p ≫ e'.hom ≫ u.hom = u.hom ≫ a) :
    (r ≪≫ e ≪≫ u).inv ≫ m ≫ (r' ≪≫ e' ≪≫ u).hom = a := by
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]
  rw [← Category.assoc m r'.hom, hn]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hs]
  simp

private lemma frame_inclusion {C : Type*} [Category C]
    {A B D O : C} (e : A ≅ O) (e' : B ≅ O) (h : B ≅ D) (f : D ≅ O)
    (m : A ⟶ B) (a : O ⟶ O) (ha : e.inv ≫ m ≫ e'.hom = a) :
    e.inv ≫ (m ≫ h.hom) ≫ f.hom = a ≫ (f.symm ≪≫ h.symm ≪≫ e').inv := by
  rw [← ha]
  simp

private lemma mono_iso_sandwich {C : Type*} [Category C]
    {A B D E F : C} (e : A ≅ B) (m : B ⟶ D) (u : D ≅ E) (v : E ≅ F)
    [Mono m] : Mono ((e.hom ≫ m ≫ u.hom) ≫ v.hom) := inferInstance

lemma tensor_inclusion_framed (J M : LineBundle X) (ι : J.sheaf ⟶ O X)
    (U : X.Opens) (e : J.sheaf.restrict U.ι ≅ O U.toScheme)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) :
    (tensorFrame J M U e f).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map (tensorInclusion J M ι) ≫ f.hom =
      (e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map ι ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom) ≫ (tensorUnitTwist M U f).inv := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let R := moduleTensorRestrict U J.sheaf M.sheaf
  let R' := moduleTensorRestrict U (O X) M.sheaf
  let E := moduleTensorIso e f
  let E' := moduleTensorIso (Scheme.Modules.restrictUnitIso U.ι) f
  let T := moduleTensorUnit (O U.toScheme)
  let a : O U.toScheme ⟶ O U.toScheme :=
    (e.inv ≫ F.map ι) ≫ (Scheme.Modules.restrictUnitIso U.ι).hom
  have hn : F.map (moduleTensorMap ι (𝟙 M.sheaf)) ≫ R'.hom =
      R.hom ≫ moduleTensorMap (F.map ι) (𝟙 (M.sheaf.restrict U.ι)) :=
    (moduleTensorRestrict_natural U ι (𝟙 M.sheaf)).trans
      (congrArg (fun q => R.hom ≫ moduleTensorMap (F.map ι) q) (F.map_id M.sheaf))
  have h₁ := (moduleTensorMap_comp e.inv (F.map ι) f.inv
    (𝟙 (M.sheaf.restrict U.ι))).symm.trans
      (congrArg (moduleTensorMap (e.inv ≫ F.map ι)) (Category.comp_id f.inv))
  have h₂ := (moduleTensorMap_comp (e.inv ≫ F.map ι)
    (Scheme.Modules.restrictUnitIso U.ι).hom f.inv f.hom).symm.trans
      (congrArg (moduleTensorMap a) f.inv_hom_id)
  have ht : E.inv ≫ moduleTensorMap (F.map ι) (𝟙 (M.sheaf.restrict U.ι)) ≫
      E'.hom = moduleTensorMap a (𝟙 (O U.toScheme)) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ E'.hom) h₁).trans h₂)
  have hs : E.inv ≫ moduleTensorMap (F.map ι) (𝟙 (M.sheaf.restrict U.ι)) ≫
      E'.hom ≫ T.hom = T.hom ≫ a := by
    have hscalar := moduleTensorUnit_scalar (X := U.toScheme) a (𝟙 (O U.toScheme))
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ T.hom) ht).trans
        (hscalar.trans (congrArg (fun q => T.hom ≫ q) (Category.comp_id a))))
  have hframe := frame_square R R' E E' T
    (F.map (moduleTensorMap ι (𝟙 M.sheaf))) _ a hn hs
  have hfinal := frame_inclusion (R ≪≫ E ≪≫ T) (R' ≪≫ E' ≪≫ T)
    (F.mapIso (moduleTensorUnit M.sheaf)) f
    (F.map (moduleTensorMap ι (𝟙 M.sheaf))) a hframe
  simpa only [tensorInclusion, tensorUnitTwist, tensorFrame] using!
    (congrArg (fun q => (tensorFrame J M U e f).inv ≫ q ≫ f.hom)
      (F.map_comp (moduleTensorMap ι (𝟙 M.sheaf)) (moduleTensorUnit M.sheaf).hom)).trans hfinal

theorem tensorInclusion_mono (J M : LineBundle X) (ι : J.sheaf ⟶ O X) [Mono ι] :
    Mono (tensorInclusion J M ι) := by
  apply PiExponent.CoherentTwist.mono_of_local
  intro x
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames J M x
  refine ⟨U.1,hx,?_⟩
  have hm : Mono ((tensorFrame J M U.1 e f).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (tensorInclusion J M ι) ≫ f.hom) := by
    erw [tensor_inclusion_framed]
    have hmap : Mono (C := U.1.toScheme.Modules)
        ((Scheme.Modules.restrictFunctor U.1.ι).map ι) :=
      @Functor.map_mono _ _ _ _ (Scheme.Modules.restrictFunctor U.1.ι)
        inferInstance _ _ ι (inferInstanceAs (Mono ι))
    exact @mono_iso_sandwich U.1.toScheme.Modules _ _ _ _ _ _ e.symm
      ((Scheme.Modules.restrictFunctor U.1.ι).map ι)
      (Scheme.Modules.restrictUnitIso U.1.ι) (tensorUnitTwist M U.1 f).symm hmap
  exact (mono_comp_iff_of_mono _ f.hom).mp
    ((mono_comp_iff_of_isIso (tensorFrame J M U.1 e f).inv _).mp hm)

lemma tensor_inclusion_ideal (J M : LineBundle X) (ι : J.sheaf ⟶ O X)
    (U : X.affineOpens) (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (f : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span {U.1.topIso.hom (endValue ((tensorFrame J M U.1 e f).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (tensorInclusion J M ι) ≫ f.hom))} =
    Ideal.span {U.1.topIso.hom (endValue (e.inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
        (Scheme.Modules.restrictUnitIso U.1.ι).hom))} := by
  erw [tensor_inclusion_framed,endValue_comp,map_mul,
    ← Ideal.span_singleton_mul_span_singleton]
  have hu : IsUnit (endValue (tensorUnitTwist M U.1 f).inv) :=
    (end_isIso_iff _).mp inferInstance
  erw [Ideal.span_singleton_eq_top.mpr (hu.map U.1.topIso.hom.hom),Ideal.mul_top]
  rfl

end
end PiExponentSeshadri.Geometry

end OAI
