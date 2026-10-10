import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.ClosedEmbedding

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial HomogeneousLocalization
open MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K]

lemma affine_evaluation_finite {R : Type} [CommRing R] {Y : Scheme}
    (f : R →+* Γ(Y,⊤)) [IsFinite (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f))] :
    f.Finite := by
  let g := Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)
  have hEq : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop = CommRingCat.ofHom f := by
    simp only [g, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  have h := g.finite_appTop.comp (RingHom.Finite.of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective)
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom.Finite at h
  simpa only [hEq, CommRingCat.hom_ofHom] using h

lemma normalized_evalAway_polyToChart {R : Type} [CommRing R]
    (k : K →+* R) (a : σ → R) (i : σ) (hi : a i = 1) :
    (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (MvPolynomial.X i)
      (by simpa only [eval₂Hom_X',hi] using (isUnit_one : IsUnit (1 : R)))).comp
      (polyToChart i) = eval₂Hom k (fun j : ChartVariables i => a j) := by
  let F := evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (MvPolynomial.X i)
    (by simpa only [eval₂Hom_X',hi] using (isUnit_one : IsUnit (1 : R)))
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, polyToChart, eval₂Hom_C]
    change F (chartConstants i r) = k r
    exact RingHom.congr_fun (evalAway_constants k a i hi) r
  · intro j
    simp only [RingHom.comp_apply, polyToChart, eval₂Hom_X']
    change F (chartCoordinate i j.val) = a j.val
    have H := evalAway_mk_clear (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (isHomogeneous_X K i)
      (show IsUnit ((eval₂Hom k a) (MvPolynomial.X i)) by simpa only [eval₂Hom_X',hi] using
        (isUnit_one : IsUnit (1 : R))) 1 (X j.val) (by simpa using isHomogeneous_X K j.val)
    simpa only [chartCoordinate, eval₂Hom_X',hi,one_pow,mul_one] using H

theorem finite_sectionsMorphism_chart {X : Scheme} {M : X.Modules}
    (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (i : σ) :
    IsAffine (SectionOpens.isoOpen (s i)).toScheme ∧
    (eval₂Hom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
      (fun j : ChartVariables i => coefficient (sectionFrame (s i))
        (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)))).Finite := by
  let V := projectiveCoordinateCover (K := K) (σ := σ)
  let U := SectionOpens.isoOpen (s i)
  let k' := U.ι.appTop.hom.comp k
  let a : σ → Γ(U.toScheme,⊤) := fun j => coefficient (sectionFrame (s i))
    (restrictSection U.ι (s j))
  have hi : a i = 1 := sectionFrame_normalized (s i)
  let f := evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k' a) (MvPolynomial.X i)
    (by simpa only [eval₂Hom_X',hi] using (isUnit_one : IsUnit (1 : Γ(U.toScheme,⊤))))
  let g := U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)
  let chart := Proj.awayι (homogeneousSubmodule σ K) (MvPolynomial.X i)
    (isHomogeneous_X K i) (show 0 < 1 by decide)
  have : IsOpenImmersion chart := V.map_prop i
  have H : IsPullback g U.ι chart (sectionsMorphism k s hs) := by
    apply IsOpenImmersion.isPullback
    · exact (sectionsMorphism_local k s hs i).trans (Category.assoc _ _ _).symm
    · have hrange : chart.opensRange =
          Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X i) :=
        Proj.opensRange_awayι _ _ (isHomogeneous_X K i) (show 0 < 1 by decide)
      rw [hrange, sectionsMorphism_preimage, Scheme.Opens.opensRange_ι]
  have hg : IsFinite g := MorphismProperty.of_isPullback H.flip inferInstance
  refine ⟨isAffine_of_isAffineHom g, ?_⟩
  have hf := (@affine_evaluation_finite _ _ U.toScheme f hg).comp (RingHom.Finite.of_surjective
    (polyToChart (R := K) i) (polynomialChartEquiv (R := K) i).symm.surjective)
  rwa [normalized_evalAway_polyToChart k' a i hi] at hf

instance boolChartUnique (i : Bool) : Unique (ChartVariables i) where
  default := ⟨!i, by cases i <;> decide⟩
  uniq j := by rcases j with ⟨j,hj⟩; cases i <;> cases j <;> simp_all

theorem finite_pencil_chart {X : Scheme} {M : X.Modules}
    (k : K →+* Γ(X,⊤)) (s : Bool → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (i : Bool) :
    IsAffine (SectionOpens.isoOpen (s i)).toScheme ∧
    (Polynomial.eval₂RingHom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
      (coefficient (sectionFrame (s i))
        (restrictSection (SectionOpens.isoOpen (s i)).ι (s (!i))))).Finite := by
  obtain ⟨hA,hf⟩ := finite_sectionsMorphism_chart k s hs i
  refine ⟨hA, ?_⟩
  have h := hf.comp (RingHom.Finite.of_surjective
    (MvPolynomial.uniqueAlgEquiv K (ChartVariables i)).symm.toRingHom
    (MvPolynomial.uniqueAlgEquiv K (ChartVariables i)).symm.surjective)
  have he : (eval₂Hom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
      (fun j : ChartVariables i => coefficient (sectionFrame (s i))
        (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)))).comp
      (MvPolynomial.uniqueAlgEquiv K (ChartVariables i)).symm.toRingHom =
      Polynomial.eval₂RingHom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
      (coefficient (sectionFrame (s i))
        (restrictSection (SectionOpens.isoOpen (s i)).ι (s (!i)))) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [MvPolynomial.uniqueAlgEquiv]
    · have hd : (default : ChartVariables i).val = !i :=
        congrArg Subtype.val (Subsingleton.elim (default : ChartVariables i)
          ⟨!i, by cases i <;> decide⟩)
      simpa [MvPolynomial.uniqueAlgEquiv] using congrArg
        (fun j => coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s j))) hd
  rwa [he] at h
end
end MaximalSeshadri.Projective
end


end
end

end OAI
