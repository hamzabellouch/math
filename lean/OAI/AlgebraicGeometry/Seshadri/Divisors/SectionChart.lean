import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.ClosedEmbedding
import OAI.AlgebraicGeometry.Seshadri.Projective.HyperplaneSection

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K] {X : Scheme}

lemma projective_factor_open (h : X ⟶ Proj (PolyGrade K σ)) (U : X.affineOpens)
    (i : σ) (φ : PolyChart (R := K) i →+* Γ(X, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        U.2.fromSpec ≫ h) :
    U.1 ≤ h ⁻¹ᵁ Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i) := by
  intro x hx
  have hx' : x ∈ (U.1 : Set X) := hx
  rw [← U.2.range_fromSpec] at hx'
  obtain ⟨y, rfl⟩ := hx'
  change h (U.2.fromSpec y) ∈ Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i)
  rw [← Scheme.Hom.comp_apply, ← hφ]
  have hh : (Spec.map (CommRingCat.ofHom φ) ≫
    Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide)) y ∈
    (Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide)).opensRange :=
      ⟨_, rfl⟩
  rwa [Proj.opensRange_awayι] at hh

def sectionFrameOn {M : X.Modules} (s : O X ⟶ M) (U : X.Opens)
    (hU : U ≤ SectionOpens.isoOpen s) : M.restrict U.ι ≅ O U.toScheme :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hU).symm).app M ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE hU) (SectionOpens.isoOpen s).ι).app M ≪≫
      restrictFrame (X.homOfLE hU) (sectionFrame s)

lemma sectionFrameOn_coefficient {M : X.Modules} (s t : O X ⟶ M) (U : X.Opens)
    (hU : U ≤ SectionOpens.isoOpen s) :
    coefficient (sectionFrameOn s U hU) (restrictSection U.ι t) =
      (X.homOfLE hU).appTop (coefficient (sectionFrame s)
        (restrictSection (SectionOpens.isoOpen s).ι t)) := by
  unfold sectionFrameOn
  rw [coefficient_transport]
  change coefficient
    ((Scheme.Modules.restrictFunctorComp (X.homOfLE hU) (SectionOpens.isoOpen s).ι).app M ≪≫
      restrictFrame (X.homOfLE hU) (sectionFrame s))
    (restrictSection U.ι t ≫ (Scheme.Modules.restrictFunctorCongr
      (X.homOfLE_ι hU).symm).hom.app M) = _
  rw [restrictSection_congr, coefficient_restrict_comp]

lemma sectionFrameOn_normalized {M : X.Modules} (s : O X ⟶ M) (U : X.Opens)
    (hU : U ≤ SectionOpens.isoOpen s) :
    coefficient (sectionFrameOn s U hU) (restrictSection U.ι s) = 1 := by
  rw [sectionFrameOn_coefficient, sectionFrame_normalized, map_one]

lemma sectionsMorphism_on {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (i : σ) (U : X.Opens) (hU : U ≤ SectionOpens.isoOpen (s i)) :
    U.ι ≫ sectionsMorphism k s hcover =
      coordinatesMap U.toScheme (U.ι.appTop.hom.comp k)
        (fun j => coefficient (sectionFrameOn (s i) U hU) (restrictSection U.ι (s j)))
        i (sectionFrameOn_normalized (s i) U hU) := by
  conv_lhs => rw [← X.homOfLE_ι hU, Category.assoc, sectionsMorphism_local,
    coordinatesMap_natural]
  congr 1
  · rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, X.homOfLE_ι]
  · funext j
    exact (sectionFrameOn_coefficient (s i) (s j) U hU).symm

lemma affine_coordinates_factor (U : X.affineOpens) (k : K →+* Γ(U.1.toScheme, ⊤))
    (a : σ → Γ(U.1.toScheme, ⊤)) (i : σ) (hi : a i = 1) :
    U.2.isoSpec.inv ≫ coordinatesMap U.1.toScheme k a i hi =
      fromUnitCoordinate (MvPolynomial.eval₂Hom (U.1.topIso.hom.hom.comp k)
        (fun j => U.1.topIso.hom (a j))) (by decide) (coordinates_X_mem i)
        (by simpa only [MvPolynomial.eval₂Hom_X', hi, map_one] using
          (isUnit_one : IsUnit (1 : Γ(X, U.1)))) := by
  rw [coordinatesMap, ← Category.assoc]
  have he : U.2.isoSpec.inv ≫ U.1.toScheme.toSpecΓ = Spec.map U.1.topIso.hom := by
    let : IsAffine U.1.toScheme := U.2
    change (Spec.map U.1.topIso.hom ≫ U.1.toScheme.isoSpec.inv) ≫ _ = _
    simp only [Category.assoc, Scheme.isoSpec_inv_toSpecΓ, Category.comp_id]
  rw [he]
  change Spec.map (CommRingCat.ofHom U.1.topIso.hom.hom) ≫ _ = _
  rw [fromUnitCoordinate_natural]
  congr 1
  exact coordinates_eval_natural _ _ _

lemma evalAway_coordinate {R : Type} [CommRing R] (k : K →+* R) (a : σ → R)
    (i : σ) (hi : a i = 1) (j : σ) :
    evalAway (MvPolynomial.eval₂Hom k a) (MvPolynomial.X i)
      (by simpa only [MvPolynomial.eval₂Hom_X', hi] using
        (isUnit_one : IsUnit (1 : R))) (chartCoordinate i j) = a j := by
  have hh := evalAway_mk_clear (MvPolynomial.eval₂Hom k a) (poly_X_mem i)
    (by simpa only [MvPolynomial.eval₂Hom_X', hi] using
        (isUnit_one : IsUnit (1 : R))) 1 (MvPolynomial.X j)
      (by simpa using (poly_X_mem (R := K) j))
  simpa only [chartCoordinate, MvPolynomial.eval₂Hom_X', hi, one_pow, mul_one] using hh

theorem sectionsMorphism_affine_equation [Fintype σ] {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
    (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (U : X.affineOpens) (i : σ) (φ : PolyChart (R := K) i →+* Γ(X, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        U.2.fromSpec ≫ sectionsMorphism k s hcover) :
    ∃ e : M.restrict U.1.ι ≅ O U.1.toScheme, ∀ t : σ → K,
      U.1.topIso.hom (coefficient e (restrictSection U.1.ι (sectionCombination k s t))) =
        ∑ j, φ (chartConstants i (t j)) * φ (chartCoordinate i j) := by
  have hU := projective_factor_open (sectionsMorphism k s hcover) U i φ hφ
  rw [sectionsMorphism_preimage] at hU
  let e := sectionFrameOn (s i) U.1 hU
  let a (j : σ) : Γ(X, U.1) :=
    U.1.topIso.hom (coefficient e (restrictSection U.1.ι (s j)))
  let kU : K →+* Γ(X, U.1) := U.1.topIso.hom.hom.comp (U.1.ι.appTop.hom.comp k)
  have hai : a i = 1 := by simp only [a, e, sectionFrameOn_normalized, map_one]
  have hφ' : φ = evalAway (MvPolynomial.eval₂Hom kU a) (MvPolynomial.X i)
      (by simpa only [MvPolynomial.eval₂Hom_X', hai] using
        (isUnit_one : IsUnit (1 : Γ(X, U.1)))) := by
    apply_fun CommRingCat.ofHom
    · apply Spec.map_injective
      rw [← cancel_mono (Proj.awayι (PolyGrade K σ) (MvPolynomial.X i)
        (poly_X_mem i) (by decide))]
      rw [hφ, ← U.2.isoSpec_inv_ι, Category.assoc, sectionsMorphism_on k s hcover i U.1 hU,
        affine_coordinates_factor]
      rfl
    · exact fun _ _ hh => congrArg CommRingCat.Hom.hom hh
  have hcoord (j : σ) : φ (chartCoordinate i j) = a j := by
    rw [hφ']
    exact evalAway_coordinate kU a i hai j
  have hconst (c : K) : φ (chartConstants i c) = kU c := by
    rw [hφ']
    exact RingHom.congr_fun (evalAway_constants kU a i hai) c
  refine ⟨e, fun t => ?_⟩
  simp only [sectionCombination, restrictSection_sum, coefficient_sum, map_sum, hconst, hcoord]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coefficient_restrict_scalar_comp, map_mul]
  rfl

end
end MaximalSeshadri.Projective
end


end
end

end OAI
