import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionNaturality
import OAI.AlgebraicGeometry.Seshadri.Sheaves.FramedPullback

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames

variable {X Y : Scheme.{0}}

lemma exists_frame_natIso_all (F G : X.Modules ⥤ Y.Modules) (v : F ≅ G)
    (uF : F.obj (O X) ≅ O Y) (uG : G.obj (O X) ≅ O Y)
    {M : X.Modules} (e : G.obj M ≅ O Y) :
    ∃ eF : F.obj M ≅ O Y, ∀ s : O X ⟶ M,
      coefficient eF (uF.inv ≫ F.map s) = coefficient e (uG.inv ≫ G.map s) := by
  let b : O Y ≅ O Y := uF.symm ≪≫ v.app (O X) ≪≫ uG
  refine ⟨v.app M ≪≫ e ≪≫ b.symm, ?_⟩
  intro s
  have h : (uF.inv ≫ F.map s) ≫ (v.app M).hom =
      b.hom ≫ (uG.inv ≫ G.map s) := by
    simp only [b, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    simp only [Iso.hom_inv_id_assoc]
    exact congrArg (fun q => uF.inv ≫ q) (v.hom.naturality s)
  change endValue (((uF.inv ≫ F.map s) ≫ (v.app M).hom) ≫ e.hom ≫ b.inv) = _
  rw [h]
  change endValue (b.hom ≫ (uG.inv ≫ G.map s ≫ e.hom) ≫ b.inv) = _
  exact endValue_conjugation b _

theorem exists_restricted_pullback_frame_all (f : Y ⟶ X) (U : X.Opens)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) :
    ∃ eF : ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
        O (f ⁻¹ᵁ U).toScheme, ∀ s : O X ⟶ M,
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
  obtain ⟨eF,he⟩ := exists_frame_natIso_all F G (pullbackRestrictNatIso f U) uF uG
    (pullbackFrame (f ∣_ U) e)
  refine ⟨eF, ?_⟩
  intro s
  have he' : coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
      coefficient (pullbackFrame (f ∣_ U) e)
        (pullbackSection (f ∣_ U) (restrictSection U.ι s)) := by
    have restrict_pullback : restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s) =
        uF.inv ≫ F.map s := by
      exact (congrArg (fun sectionMap =>
        (Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι).inv ≫ sectionMap)
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map_comp
          (pullbackUnitIso f).inv ((Scheme.Modules.pullback f).map s))).trans
        (Category.assoc _ _ _).symm
    have pullback_restrict : pullbackSection (f ∣_ U) (restrictSection U.ι s) =
        uG.inv ≫ G.map s := by
      exact (congrArg (fun sectionMap => (pullbackUnitIso (f ∣_ U)).inv ≫ sectionMap)
        ((Scheme.Modules.pullback (f ∣_ U)).map_comp
          (Scheme.Modules.restrictUnitIso U.ι).inv
          ((Scheme.Modules.restrictFunctor U.ι).map s))).trans
        (Category.assoc _ _ _).symm
    exact (congrArg (coefficient eF) restrict_pullback).trans
      ((he s).trans (congrArg (coefficient (pullbackFrame (f ∣_ U) e))
        pullback_restrict).symm)
  rw [he', coefficient_pullback]

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K] {X Y : Scheme.{0}}

lemma pullback_isoOpen_le {M : X.Modules} (s : O X ⟶ M) (f : Y ⟶ X) :
    f ⁻¹ᵁ SectionOpens.isoOpen s ≤ SectionOpens.isoOpen (pullbackSection f s) := by
  let U := SectionOpens.isoOpen s
  obtain ⟨e,he⟩ := exists_restricted_pullback_frame_all f U (sectionFrame s)
  have hn : coefficient e (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) = 1 := by
    rw [he,sectionFrame_normalized,map_one]
  have hp : (f ⁻¹ᵁ U).ι ⁻¹ᵁ SectionOpens.isoOpen (pullbackSection f s) = ⊤ := by
    rw [preimage_isoOpen (pullbackSection f s) (f ⁻¹ᵁ U).ι e, hn]
    exact (isUnit_iff_basicOpen_top _).mp isUnit_one
  intro x hx
  have h : (⟨x,hx⟩ : (f ⁻¹ᵁ U).toScheme) ∈
      (f ⁻¹ᵁ U).ι ⁻¹ᵁ SectionOpens.isoOpen (pullbackSection f s) := by rw [hp]; trivial
  exact h

lemma pullback_sections_cover {M : X.Modules} (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (f : Y ⟶ X) :
    (⨆ i, SectionOpens.isoOpen (pullbackSection f (s i))) = ⊤ := by
  apply top_le_iff.mp
  rw [← Scheme.Hom.preimage_top f, ← hs, Scheme.Hom.preimage_iSup]
  exact iSup_mono fun i => pullback_isoOpen_le (s i) f

theorem sectionsMorphism_pullback {M : X.Modules} (k : K →+* Γ(X,⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (f : Y ⟶ X) :
    f ≫ sectionsMorphism k s hs =
      sectionsMorphism (f.appTop.hom.comp k) (fun i => pullbackSection f (s i))
        (pullback_sections_cover s hs f) := by
  let t (i : σ) := pullbackSection f (s i)
  let ht := pullback_sections_cover s hs f
  have hc : (⨆ i, f ⁻¹ᵁ SectionOpens.isoOpen (s i)) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup,hs,Scheme.Hom.preimage_top]
  apply (Y.openCoverOfIsOpenCover (fun i => f ⁻¹ᵁ SectionOpens.isoOpen (s i)) hc).hom_ext
  intro i
  change σ at i
  let U := SectionOpens.isoOpen (s i)
  obtain ⟨e,he⟩ := exists_restricted_pullback_frame_all f U (sectionFrame (s i))
  have hi : coefficient e (restrictSection (f ⁻¹ᵁ U).ι (t i)) = 1 := by
    rw [he,sectionFrame_normalized,map_one]
  change (f ⁻¹ᵁ U).ι ≫ (f ≫ sectionsMorphism k s hs) =
    (f ⁻¹ᵁ U).ι ≫ sectionsMorphism (f.appTop.hom.comp k) t ht
  rw [← Category.assoc, ← morphismRestrict_ι f U, Category.assoc,
    sectionsMorphism_local, coordinatesMap_natural,
    sectionsMorphism_frame _ t ht (f ⁻¹ᵁ U).ι e i hi]
  congr 1
  · rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop,
      morphismRestrict_ι f U, Scheme.Hom.comp_appTop]
    rfl
  · exact (funext fun j => he (s j)).symm
end
end MaximalSeshadri.Projective
end


end
end

end OAI
