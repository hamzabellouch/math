import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.HyperplanePullback
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionNaturality

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.IdealPullback
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

def sectionIdeal {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → K) : X.IdealSheafData :=
  (ambientHyperplane v).comap (sectionsMorphism k s hs)

lemma sectionIdeal_restrict {Y : Scheme} {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → K) (φ : Y ⟶ X) [IsOpenImmersion φ] :
    (sectionIdeal k s hs v).comap φ = sectionIdeal (φ.appTop.hom.comp k)
      (fun i => restrictSection φ (s i)) (restricted_sections_cover s hs φ) v := by
  rw [sectionIdeal, ← Scheme.IdealSheafData.comap_comp, sectionsMorphism_restrict]
  rfl

lemma sectionIdeal_on {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → K) (U : X.affineOpens) (i : σ)
    (hU : U.1 ≤ SectionOpens.isoOpen (s i)) :
    (sectionIdeal k s hs v).ideal U = Ideal.span
      {U.1.topIso.hom (coefficient (sectionFrameOn (s i) U.1 hU)
        (restrictSection U.1.ι (sectionCombination k s v)))} := by
  let e := sectionFrameOn (s i) U.1 hU
  let kU := U.1.topIso.hom.hom.comp (U.1.ι.appTop.hom.comp k)
  let a (j : σ) := U.1.topIso.hom (coefficient e (restrictSection U.1.ι (s j)))
  have hai : a i = 1 := by simp only [a, e, sectionFrameOn_normalized, map_one]
  let φ : PolyChart (R := K) i →+* Γ(X, U.1) :=
    evalAway (eval₂Hom kU a) (MvPolynomial.X i)
      (by simpa only [eval₂Hom_X', hai] using (isUnit_one : IsUnit (1 : Γ(X, U.1))))
  have hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        U.2.fromSpec ≫ sectionsMorphism k s hs := by
    rw [← U.2.isoSpec_inv_ι, Category.assoc, sectionsMorphism_on k s hs i U.1 hU,
      affine_coordinates_factor]
    rfl
  have hcoord (j : σ) : φ (chartCoordinate i j) = a j := evalAway_coordinate kU a i hai j
  have hconst (c : K) : φ (chartConstants i c) = kU c :=
    RingHom.congr_fun (evalAway_constants kU a i hai) c
  rw [sectionIdeal, ambientHyperplane_comap_equation _ v U i φ hφ]
  congr 2
  simp only [sectionCombination, restrictSection_sum, coefficient_sum, map_sum,
    hconst, hcoord]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coefficient_restrict_scalar_comp, map_mul]
  rfl

lemma coefficient_span_frame {M : X.Modules} (e f : M ≅ O X) (s : O X ⟶ M)
    {R : Type} [CommRing R] (ρ : Γ(X, ⊤) →+* R) :
    Ideal.span ({ρ (coefficient e s)} : Set R) =
      Ideal.span {ρ (coefficient f s)} := by
  rw [coefficient_change e f, map_mul, ← Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_eq_top.mpr ((frameChange e f).isUnit.map ρ), Ideal.top_mul]

lemma sectionIdeal_on_frame {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → K) (U : X.affineOpens) (i : σ)
    (hU : U.1 ≤ SectionOpens.isoOpen (s i))
    (e : M.restrict U.1.ι ≅ O U.1.toScheme) :
    (sectionIdeal k s hs v).ideal U = Ideal.span
      {U.1.topIso.hom (coefficient e (restrictSection U.1.ι (sectionCombination k s v)))} := by
  rw [sectionIdeal_on k s hs v U i hU]
  exact coefficient_span_frame _ e _ U.1.topIso.hom.hom

end
end MaximalSeshadri.Projective
end


end
end

end OAI
