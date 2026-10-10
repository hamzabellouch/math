import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.SectionPullback

namespace OAI

noncomputable section

                                        

namespace MaximalSeshadri.Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames

variable {X Y : Scheme.{0}}

lemma endValue_conjugation (b : O Y ≅ O Y) (a : O Y ⟶ O Y) :
    endValue (b.hom ≫ a ≫ b.inv) = endValue a := by
  rw [endValue_comp, endValue_comp]
  have hb : endValue b.hom * endValue b.inv = 1 := by
    rw [← endValue_comp, b.hom_inv_id, endValue_id]
  calc
    endValue b.hom * (endValue a * endValue b.inv) =
      endValue a * (endValue b.hom * endValue b.inv) := by ring
    _ = endValue a := by rw [hb, mul_one]

lemma exists_frame_natIso (F G : X.Modules ⥤ Y.Modules) (v : F ≅ G)
    (uF : F.obj (O X) ≅ O Y) (uG : G.obj (O X) ≅ O Y)
    {M : X.Modules} (e : G.obj M ≅ O Y) (s : O X ⟶ M) :
    ∃ eF : F.obj M ≅ O Y,
      coefficient eF (uF.inv ≫ F.map s) = coefficient e (uG.inv ≫ G.map s) := by
  let b : O Y ≅ O Y := uF.symm ≪≫ v.app (O X) ≪≫ uG
  refine ⟨v.app M ≪≫ e ≪≫ b.symm, ?_⟩
  have h : (uF.inv ≫ F.map s) ≫ (v.app M).hom =
      b.hom ≫ (uG.inv ≫ G.map s) := by
    simp only [b, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    simp only [Iso.hom_inv_id_assoc]
    exact congrArg (fun q => uF.inv ≫ q) (v.hom.naturality s)
  change endValue (((uF.inv ≫ F.map s) ≫ (v.app M).hom) ≫ e.hom ≫ b.inv) = _
  rw [h]
  change endValue (b.hom ≫ (uG.inv ≫ G.map s ≫ e.hom) ≫ b.inv) = _
  exact endValue_conjugation b _

def pullbackRestrictNatIso (f : Y ⟶ X) (U : X.Opens) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
    (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι) ≪≫
  Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f ≪≫
  Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm ≪≫
  (Scheme.Modules.pullbackComp (f ∣_ U) U.ι).symm ≪≫
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
    (Scheme.Modules.pullback (f ∣_ U))
theorem exists_restricted_pullback_frame (f : Y ⟶ X) (U : X.Opens)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) (s : O X ⟶ M) :
    ∃ eF : ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
        O (f ⁻¹ᵁ U).toScheme,
      coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
        (f ∣_ U).appTop (coefficient e (restrictSection U.ι s)) := by
  let F := Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι
  let G := Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U)
  let uF : F.obj (O X) ≅ O (f ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).mapIso (pullbackUnitIso f) ≪≫
      Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι
  let uG : G.obj (O X) ≅ O (f ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.pullback (f ∣_ U)).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
      pullbackUnitIso (f ∣_ U)
  obtain ⟨eF,he⟩ := exists_frame_natIso F G (pullbackRestrictNatIso f U) uF uG
    (pullbackFrame (f ∣_ U) e) s
  refine ⟨eF, ?_⟩
  have he' : coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
      coefficient (pullbackFrame (f ∣_ U) e)
        (pullbackSection (f ∣_ U) (restrictSection U.ι s)) := by
    have leftSection : uF.inv ≫ F.map s =
        restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s) := by
      dsimp only [uF, F, restrictSection, pullbackSection, Iso.trans,
        Functor.mapIso, Functor.comp]
      exact (Category.assoc _ _ _).trans
        (congrArg (fun sectionMap => (Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι).inv ≫
          sectionMap) ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map_comp
            (pullbackUnitIso f).inv ((Scheme.Modules.pullback f).map s)).symm)
    have rightSection : uG.inv ≫ G.map s =
        pullbackSection (f ∣_ U) (restrictSection U.ι s) := by
      dsimp only [uG, G, restrictSection, pullbackSection, Iso.trans,
        Functor.mapIso, Functor.comp]
      exact (Category.assoc _ _ _).trans
        (congrArg (fun sectionMap => (pullbackUnitIso (f ∣_ U)).inv ≫ sectionMap)
          ((Scheme.Modules.pullback (f ∣_ U)).map_comp
            (Scheme.Modules.restrictUnitIso U.ι).inv
            ((Scheme.Modules.restrictFunctor U.ι).map s)).symm)
    exact (congrArg (coefficient eF) leftSection).symm.trans
      (he.trans (congrArg (coefficient (pullbackFrame (f ∣_ U) e)) rightSection))
  rw [he', coefficient_pullback]

end MaximalSeshadri.Geometry

end

end OAI
