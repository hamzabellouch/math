import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.SectionMaps

namespace OAI

section
noncomputable section
                                           
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K] {X Y : Scheme}

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

lemma restricted_sections_cover {M : X.Modules} (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (φ : Y ⟶ X) [IsOpenImmersion φ] :
    (⨆ i, SectionOpens.isoOpen (restrictSection φ (s i))) = ⊤ := by
  simp_rw [isoOpen_restrictSection]
  rw [← Scheme.Hom.preimage_iSup, hs, Scheme.Hom.preimage_top]

lemma coefficient_composite_frame {Z : Scheme} {M : X.Modules}
    (φ : Y ⟶ X) (ψ : Z ⟶ Y) [IsOpenImmersion φ] [IsOpenImmersion ψ]
    (e : (M.restrict φ).restrict ψ ≅ O Z) (s : O X ⟶ M) :
    coefficient ((Scheme.Modules.restrictFunctorComp ψ φ).app M ≪≫ e)
      (restrictSection (ψ ≫ φ) s) = coefficient e (restrictSection ψ (restrictSection φ s)) := by
  rw [coefficient_transport]
  change coefficient e (restrictSection (ψ ≫ φ) s ≫
    (Scheme.Modules.restrictFunctorComp ψ φ).hom.app M) = _
  rw [restrictSection_comp]

lemma sectionsMorphism_restrict {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (φ : Y ⟶ X) [IsOpenImmersion φ] :
    φ ≫ sectionsMorphism k s hs =
      sectionsMorphism (φ.appTop.hom.comp k) (fun i => restrictSection φ (s i))
        (restricted_sections_cover s hs φ) := by
  let t (i : σ) := restrictSection φ (s i)
  let ht := restricted_sections_cover s hs φ
  apply (Y.openCoverOfIsOpenCover (fun i => SectionOpens.isoOpen (t i)) ht).hom_ext
  intro i
  change σ at i
  let U := SectionOpens.isoOpen (t i)
  let e := (Scheme.Modules.restrictFunctorComp U.ι φ).app M ≪≫ sectionFrame (t i)
  have he (j : σ) : coefficient e (restrictSection (U.ι ≫ φ) (s j)) =
      coefficient (sectionFrame (t i)) (restrictSection U.ι (t j)) :=
    coefficient_composite_frame φ U.ι (sectionFrame (t i)) (s j)
  have hi : coefficient e (restrictSection (U.ι ≫ φ) (s i)) = 1 := by
    rw [he, sectionFrame_normalized]
  change U.ι ≫ (φ ≫ sectionsMorphism k s hs) =
    U.ι ≫ sectionsMorphism (φ.appTop.hom.comp k) t ht
  rw [← Category.assoc, sectionsMorphism_frame k s hs (U.ι ≫ φ) e i hi,
    sectionsMorphism_local]
  congr 1
  exact funext he

end
end MaximalSeshadri.Projective

end


end
end

end OAI
