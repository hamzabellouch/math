import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates
import OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [CommRing K] {X Y : Scheme.{0}}

lemma sectionsMorphism_frame {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (φ : Y ⟶ X) [IsOpenImmersion φ] (e : M.restrict φ ≅ O Y)
    (i : σ) (hi : coefficient e (restrictSection φ (s i)) = 1) :
    φ ≫ sectionsMorphism k s hs =
      coordinatesMap Y (φ.appTop.hom.comp k)
        (fun j => coefficient e (restrictSection φ (s j))) i hi := by
  let U := SectionOpens.isoOpen (s i)
  have hp : φ ⁻¹ᵁ U = ⊤ := by
    rw [show U = SectionOpens.isoOpen (s i) from rfl, preimage_isoOpen (s i) φ e, hi]
    exact (isUnit_iff_basicOpen_top _).mp isUnit_one
  have hr : Set.range φ ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have h : y ∈ φ ⁻¹ᵁ U := by rw [hp]; trivial
    exact h
  let l := IsOpenImmersion.lift U.ι φ hr
  have hl : l ≫ U.ι = φ := IsOpenImmersion.lift_fac U.ι φ hr
  let : IsOpenImmersion l := IsOpenImmersion.of_comp l U.ι
  obtain ⟨c, hc⟩ := overlap_coefficients φ U.ι (𝟙 Y) l (by simpa using hl.symm)
    e (sectionFrame (s i))
  have hci : (c : Γ(Y, ⊤)) = 1 := by
    have h := hc (s i)
    simpa only [U, sectionFrame_normalized, map_one, hi, Scheme.Hom.id_appTop,
      CommRingCat.id_apply, mul_one] using h.symm
  have hc' (j : σ) : l.appTop (coefficient (sectionFrame (s i))
      (restrictSection U.ι (s j))) = coefficient e (restrictSection φ (s j)) := by
    simpa only [hci, Scheme.Hom.id_appTop, CommRingCat.id_apply, one_mul] using hc (s j)
  conv_lhs => rw [← hl, Category.assoc, sectionsMorphism_local, coordinatesMap_natural]
  congr 1
  · rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, hl]
  · exact funext hc'

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
  let U := SectionOpens.isoOpen (s i)
  obtain ⟨e,he⟩ := exists_restricted_pullback_frame_all f U (sectionFrame (s i))
  have hi : coefficient e (restrictSection (f ⁻¹ᵁ U).ι (t i)) = 1 := by
    rw [he,sectionFrame_normalized,map_one]
  change (f ⁻¹ᵁ U).ι ≫ (f ≫ sectionsMorphism k s hs) =
    (f ⁻¹ᵁ U).ι ≫ sectionsMorphism (f.appTop.hom.comp k) t ht
  erw [← Category.assoc, ← morphismRestrict_ι f U, Category.assoc,
    sectionsMorphism_local k s hs i, coordinatesMap_natural,
    sectionsMorphism_frame _ t ht (f ⁻¹ᵁ U).ι e i hi]
  congr 1
  · rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop,
      morphismRestrict_ι f U, Scheme.Hom.comp_appTop]
    rfl
  · exact (funext fun j => he (s j)).symm
end
end PiExponentSeshadri.Projective

end OAI
