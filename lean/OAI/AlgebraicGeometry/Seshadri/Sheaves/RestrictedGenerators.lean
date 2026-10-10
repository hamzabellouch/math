import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.AmpleEmbedding
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionNaturality

namespace OAI

section
noncomputable section
                                              
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K] {X Y : Scheme}

lemma section_chart_generators_frame {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)] (i : σ)
    (φ : Y ⟶ X) [IsOpenImmersion φ]
    (hφ : φ.opensRange = SectionOpens.isoOpen (s i))
    (e : M.restrict φ ≅ O Y) (hi : coefficient e (restrictSection φ (s i)) = 1) :
    IsAffine Y ∧ Function.Surjective (eval₂Hom (φ.appTop.hom.comp k)
      (fun j => coefficient e (restrictSection φ (s j)))) := by
  let U := SectionOpens.isoOpen (s i)
  have hr : Set.range φ = Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact congrArg (fun V : X.Opens => (V : Set X)) hφ
  let a := IsOpenImmersion.isoOfRangeEq φ U.ι hr
  have ha : a.hom ≫ U.ι = φ := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  obtain ⟨hu, hgen⟩ := sectionsMorphism_chart_generators k s hs i
  let : IsAffine U.toScheme := hu
  refine ⟨IsAffine.of_isIso a.hom, ?_⟩
  obtain ⟨c, hc⟩ := overlap_coefficients φ U.ι (𝟙 Y) a.hom
    (by simpa using ha.symm) e (sectionFrame (s i))
  have hci : (c : Γ(Y, ⊤)) = 1 := by
    have h := hc (s i)
    simpa only [U, sectionFrame_normalized, map_one, hi, Scheme.Hom.id_appTop,
      CommRingCat.id_apply, mul_one] using h.symm
  have hc' (j : σ) : a.hom.appTop (coefficient (sectionFrame (s i))
      (restrictSection U.ι (s j))) = coefficient e (restrictSection φ (s j)) := by
    simpa only [hci, Scheme.Hom.id_appTop, CommRingCat.id_apply, one_mul] using hc (s j)
  have hsurj := (ConcreteCategory.bijective_of_isIso
    (Scheme.Γ.mapIso a.op).hom).surjective.comp hgen
  have he : a.hom.appTop.hom.comp
      (eval₂Hom (U.ι.appTop.hom.comp k) (fun j => coefficient (sectionFrame (s i))
        (restrictSection U.ι (s j)))) =
      eval₂Hom (φ.appTop.hom.comp k) (fun j => coefficient e (restrictSection φ (s j))) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp only [RingHom.comp_apply, eval₂Hom_C]
      change (U.ι.appTop ≫ a.hom.appTop) (k b) = φ.appTop (k b)
      rw [← Scheme.Hom.comp_appTop, ha]
    · intro j
      simp only [RingHom.comp_apply, eval₂Hom_X']
      exact hc' j
  change Function.Surjective (a.hom.appTop.hom.comp _) at hsurj
  rw [← he]
  exact hsurj

lemma restricted_chart_generators {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)] (V : X.Opens) (i : σ)
    (hiV : SectionOpens.isoOpen (s i) ≤ V) :
    let t (j : σ) := restrictSection V.ι (s j)
    let U := SectionOpens.isoOpen (t i)
    IsAffine U.toScheme ∧ Function.Surjective
      (eval₂Hom (U.ι.appTop.hom.comp (V.ι.appTop.hom.comp k))
        (fun j => coefficient (sectionFrame (t i)) (restrictSection U.ι (t j)))) := by
  let t (j : σ) := restrictSection V.ι (s j)
  let U := SectionOpens.isoOpen (t i)
  let φ := U.ι ≫ V.ι
  let e := (Scheme.Modules.restrictFunctorComp U.ι V.ι).app M ≪≫ sectionFrame (t i)
  have hc (j : σ) : coefficient e (restrictSection φ (s j)) =
      coefficient (sectionFrame (t i)) (restrictSection U.ι (t j)) :=
    coefficient_composite_frame V.ι U.ι (sectionFrame (t i)) (s j)
  have hnorm : coefficient e (restrictSection φ (s i)) = 1 := by
    rw [hc, sectionFrame_normalized]
  have hr : φ.opensRange = SectionOpens.isoOpen (s i) := by
    ext x
    change (∃ y : U, φ y = x) ↔ x ∈ SectionOpens.isoOpen (s i)
    constructor
    · rintro ⟨y, rfl⟩
      have hy : y.val ∈ V.ι ⁻¹ᵁ SectionOpens.isoOpen (s i) := by
        rw [← isoOpen_restrictSection]
        exact y.property
      exact hy
    · intro hx
      have hxV : x ∈ V := hiV hx
      have hxU : (⟨x, hxV⟩ : V) ∈ U := by
        change (⟨x, hxV⟩ : V) ∈ SectionOpens.isoOpen (restrictSection V.ι (s i))
        rw [isoOpen_restrictSection]
        exact hx
      exact ⟨⟨⟨x, hxV⟩, hxU⟩, rfl⟩
  obtain ⟨haf, hgen⟩ := section_chart_generators_frame k s hs i φ hr e hnorm
  refine ⟨haf, ?_⟩
  have hk : φ.appTop.hom.comp k = U.ι.appTop.hom.comp (V.ι.appTop.hom.comp k) := by
    rw [show φ.appTop = V.ι.appTop ≫ U.ι.appTop from Scheme.Hom.comp_appTop _ _,
      CommRingCat.hom_comp, RingHom.comp_assoc]
  rw [hk] at hgen
  simpa only [hc] using hgen

end
end MaximalSeshadri.Projective

end


end
end

end OAI
