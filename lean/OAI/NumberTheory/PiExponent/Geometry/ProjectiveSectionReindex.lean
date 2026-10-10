import OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedSections

namespace OAI

noncomputable section

universe u

namespace PiExponentSeshadri.Projective

section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type u} [CommRing K]

lemma reindex_polynomial_irrelevant_le :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule σ K)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X (R := K) : σ → MvPolynomial σ K)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  change p ∈ idealOfVars σ K
  rw [← pow_one (idealOfVars σ K), mem_pow_idealOfVars_iff]
  intro d hd
  change 1 ≤ d.sum fun _ v => v
  rw [Finsupp.sum, ← hp.degree_eq_sum_deg_support hd]
  exact hn

def reindexCoordinateCover : (Proj (homogeneousSubmodule σ K)).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan _ (X (R := K))
    (m := fun _ => 1) (fun i => isHomogeneous_X K i) (fun _ => by decide)
    reindex_polynomial_irrelevant_le

end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames MvPolynomial
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem sectionsMorphism_isClosedImmersion {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (haff : ∀ i, IsAffine (SectionOpens.isoOpen (s i)).toScheme)
    (hgen : ∀ i, Function.Surjective
      (eval₂Hom (((SectionOpens.isoOpen (s i)).ι.appTop.hom).comp k)
        (fun j => coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s j))))) :
    IsClosedImmersion (sectionsMorphism k s hcover) := by
  let V := reindexCoordinateCover (K := K) (σ := σ)
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) V.openCover
  intro i
  change σ at i
  let U := SectionOpens.isoOpen (s i)
  let : IsAffine U.toScheme := haff i
  let k' := U.ι.appTop.hom.comp k
  let a : σ → Γ(U.toScheme, ⊤) := fun j => coefficient (sectionFrame (s i)) (restrictSection U.ι (s j))
  have hi : a i = 1 := sectionFrame_normalized (s i)
  let g : U.toScheme ⟶ Spec (CommRingCat.of
      (HomogeneousLocalization.Away (homogeneousSubmodule σ K) (MvPolynomial.X i))) :=
    U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k' a) (MvPolynomial.X i)
      (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : Γ(U.toScheme, ⊤))))))
  have hg : IsClosedImmersion g := normalized_coordinates_closed k' a i hi (hgen i)
  have hV : IsOpenImmersion (V.f i) := by
    exact inferInstanceAs (IsOpenImmersion
      (Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide)))
  have H : IsPullback g U.ι (V.f i) (sectionsMorphism k s hcover) := by
    apply @IsOpenImmersion.isPullback _ _ _ _ g U.ι (V.f i)
      (sectionsMorphism k s hcover) (inferInstanceAs (IsOpenImmersion U.ι)) hV
    · exact (sectionsMorphism_local k s hcover i).trans (Category.assoc _ _ _).symm
    · change _ ⁻¹ᵁ (Proj.awayι (homogeneousSubmodule σ K) (MvPolynomial.X i) _ _).opensRange = _
      erw [Proj.opensRange_awayι, sectionsMorphism_preimage, Scheme.Opens.opensRange_ι]
  change IsClosedImmersion (pullback.snd (sectionsMorphism k s hcover) (V.f i))
  have hcomp : IsClosedImmersion (H.flip.isoPullback.inv ≫ g) :=
    @IsClosedImmersion.comp _ _ _ _ _
      (inferInstanceAs (IsClosedImmersion H.flip.isoPullback.inv)) hg
  exact H.flip.isoPullback_inv_snd ▸ hcomp

end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open HomogeneousLocalization PiExponentSeshadri.Frames
open scoped AlgebraicGeometry
variable {K R σ : Type u} [CommRing K] [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma normalized_eval₂_of_evalAway (k : K →+* R) (a : σ → R) (i : σ) (hi : a i = 1)
    (h : Function.Surjective (evalAway (𝒜 := homogeneousSubmodule σ K)
      (eval₂Hom k a) (MvPolynomial.X i)
        (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R))))) :
    Function.Surjective (eval₂Hom k a) := by
  intro r
  obtain ⟨x, hx⟩ := h r
  obtain ⟨n, q, hq, rfl⟩ := Away.mk_surjective (homogeneousSubmodule σ K)
    (isHomogeneous_X K i) x
  refine ⟨q, ?_⟩
  have he := evalAway_mk_clear (eval₂Hom k a) (isHomogeneous_X K i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R))) n q hq
  simpa only [hx, eval₂Hom_X', hi, one_pow, mul_one] using he.symm

lemma affine_evaluation_surjective {Y : Scheme.{u}} (f : R →+* Γ(Y, ⊤))
    [IsClosedImmersion (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f))] :
    Function.Surjective f := by
  let g := Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)
  have hg := (IsClosedImmersion.isAffine_surjective_of_isAffine g).2
  have hEq : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop = CommRingCat.ofHom f := by
    simp only [g, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  have hh := hg.comp (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective
  change Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom at hh
  simpa only [hEq, CommRingCat.hom_ofHom] using hh

theorem sectionsMorphism_chart_generators {X : Scheme.{u}} {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)] (i : σ) :
    IsAffine (SectionOpens.isoOpen (s i)).toScheme ∧ Function.Surjective
      (eval₂Hom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
        (fun j => coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)))) := by
  let V := reindexCoordinateCover (K := K) (σ := σ)
  let U := SectionOpens.isoOpen (s i)
  let k' := U.ι.appTop.hom.comp k
  let a : σ → Γ(U.toScheme, ⊤) := fun j => coefficient (sectionFrame (s i)) (restrictSection U.ι (s j))
  have hi : a i = 1 := sectionFrame_normalized (s i)
  let f := evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k' a) (MvPolynomial.X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : Γ(U.toScheme, ⊤))))
  let g : U.toScheme ⟶ Spec (CommRingCat.of
      (HomogeneousLocalization.Away (homogeneousSubmodule σ K) (MvPolynomial.X i))) :=
    U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)
  have hV : IsOpenImmersion (V.f i) := by
    exact inferInstanceAs (IsOpenImmersion
      (Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide)))
  have H : IsPullback g U.ι (V.f i) (sectionsMorphism k s hs) := by
    apply @IsOpenImmersion.isPullback _ _ _ _ g U.ι (V.f i)
      (sectionsMorphism k s hs) (inferInstanceAs (IsOpenImmersion U.ι)) hV
    · exact (sectionsMorphism_local k s hs i).trans (Category.assoc _ _ _).symm
    · change _ ⁻¹ᵁ (Proj.awayι (homogeneousSubmodule σ K) (MvPolynomial.X i) _ _).opensRange = _
      erw [Proj.opensRange_awayι, sectionsMorphism_preimage, Scheme.Opens.opensRange_ι]
  have hg : IsClosedImmersion g :=
    MorphismProperty.of_isPullback H.flip
      (inferInstanceAs (IsClosedImmersion (sectionsMorphism k s hs)))
  refine ⟨(IsClosedImmersion.isAffine_surjective_of_isAffine g).1, ?_⟩
  exact normalized_eval₂_of_evalAway k' a i hi (@affine_evaluation_surjective _ _ U.toScheme f hg)

end

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open PiExponentSeshadri.Frames
open scoped AlgebraicGeometry
variable {K σ τ : Type u} [CommRing K] {X : Scheme.{u}} {M : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

lemma eval₂_surjective_reindex {R : Type u} [CommRing R] (k : K →+* R)
    (a : σ → R) (e : τ ≃ σ) (h : Function.Surjective (eval₂Hom k a)) :
    Function.Surjective (eval₂Hom k (a ∘ e)) := by
  intro r
  obtain ⟨p, hp⟩ := h r
  refine ⟨rename e.symm p, ?_⟩
  change eval₂ k (a ∘ e) (rename e.symm p) = r
  rw [MvPolynomial.eval₂_rename]
  change eval₂ k a p = r at hp
  simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using hp

theorem sectionsMorphism_reindex_closed (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)] (e : τ ≃ σ)
    (ht : (⨆ i, SectionOpens.isoOpen (s (e i))) = ⊤) :
    IsClosedImmersion (sectionsMorphism k (s ∘ e) ht) := by
  apply sectionsMorphism_isClosedImmersion
  · intro i
    exact (sectionsMorphism_chart_generators k s hs (e i)).1
  · intro i
    let U := SectionOpens.isoOpen (s (e i))
    let k' : K →+* Γ(U.toScheme, ⊤) := U.ι.appTop.hom.comp k
    let a : σ → Γ(U.toScheme, ⊤) := fun j =>
      coefficient (sectionFrame (s (e i))) (restrictSection U.ι (s j))
    have h : Function.Surjective (eval₂Hom k' a) :=
      (sectionsMorphism_chart_generators k s hs (e i)).2
    change Function.Surjective (eval₂Hom k' (a ∘ e))
    exact eval₂_surjective_reindex k' a e h

end PiExponentSeshadri.Projective

end

end OAI
