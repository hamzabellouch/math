import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.PolynomialCharts
import OAI.AlgebraicGeometry.Seshadri.Geometry.GeneratedEtaleCoordinates

namespace OAI

section
noncomputable section
                                              

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme} {σ : Type}

lemma affine_restriction_etale (U V : X.affineOpens) (e : U.1 ≤ V.1) :
    (X.presheaf.map (homOfLE e).op).hom.Etale := by
  have hU : IsAffineOpen U.1 := U.2
  have hV : IsAffineOpen V.1 := V.2
  have he := hV.map_fromSpec hU (homOfLE e).op
  have : IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE e).op) ≫ hV.fromSpec) := by
    rw [he]
    infer_instance
  let : IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE e).op)) :=
    IsOpenImmersion.of_comp _ hV.fromSpec
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp inferInstance

lemma awayToSection_awayι (i : σ) :
    Spec.map (Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i)) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
      (Proj.isAffineOpen_basicOpen (PolyGrade K σ) _ (poly_X_mem i) (by decide)).fromSpec := by
  let hV := Proj.isAffineOpen_basicOpen (PolyGrade K σ) _ (poly_X_mem i) (by decide)
  rw [← cancel_epi hV.isoSpec.hom, ← Category.assoc, hV.isoSpec_hom]
  change Proj.basicOpenToSpec _ _ ≫ _ = _
  rw [← Proj.basicOpenIsoSpec_hom _ _ (poly_X_mem i) (by decide),
    Proj.awayι, Iso.hom_inv_id_assoc]
  exact hV.toSpecΓ_fromSpec.symm

theorem closed_projective_affine_surjective (h : X ⟶ Proj (PolyGrade K σ))
    [IsClosedImmersion h] (i : σ) :
    ∃ (U : X.affineOpens) (φ : PolyChart (R := K) i →+* Γ(X, U.1)),
      U.1 = h ⁻¹ᵁ Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i) ∧
      Function.Surjective φ ∧
      Spec.map (CommRingCat.ofHom φ) ≫
        Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
          U.2.fromSpec ≫ h := by
  let V := Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i)
  have hV : IsAffineOpen V := Proj.isAffineOpen_basicOpen _ _ (poly_X_mem i) (by decide)
  let U : X.affineOpens := ⟨h ⁻¹ᵁ V, hV.preimage h⟩
  let e := Proj.basicOpenIsoAway (PolyGrade K σ) _ (poly_X_mem i) (by decide)
  let φ : PolyChart (R := K) i →+* Γ(X, U.1) := (h.app V).hom.comp e.hom.hom
  refine ⟨U, φ, rfl, ?_, ?_⟩
  · exact (h.app_surjective V hV).comp (ConcreteCategory.bijective_of_isIso e.hom).surjective
  · change Spec.map (e.hom ≫ h.app V) ≫ _ = _
    rw [Spec.map_comp, Category.assoc]
    have he : e.hom = Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i) := rfl
    rw [he, awayToSection_awayι]
    rw [Scheme.Hom.app_eq_appLE]
    exact hV.SpecMap_appLE_fromSpec h U.2 le_rfl

open KaehlerDifferential MaximalSeshadri.AlgebraicJets

lemma differentials_span_projective_chart {A : Type} [CommRing A] [Algebra K A]
    (i : σ) (φ : PolyChart (R := K) i →+* A) (hφ : Function.Surjective φ)
    (hconst : ∀ c, φ (chartConstants i c) = algebraMap K A c) :
    Submodule.span A (Set.range (fun j : ChartVariables i =>
      D K A (-φ (chartCoordinate i j.1)))) = ⊤ := by
  have he : (MvPolynomial.aeval (R := K)
      (fun j : ChartVariables i => φ (chartCoordinate i j.1))).toRingHom =
      φ.comp (polyToChart i) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change MvPolynomial.aeval _ (MvPolynomial.C c) = φ (polyToChart i (MvPolynomial.C c))
      rw [MvPolynomial.aeval_C]
      simpa only [polyToChart, MvPolynomial.eval₂Hom_C] using (hconst c).symm
    · intro j
      change MvPolynomial.aeval _ (MvPolynomial.X j) = φ (polyToChart i (MvPolynomial.X j))
      rw [MvPolynomial.aeval_X, polyToChart, MvPolynomial.eval₂Hom_X']
  have hp : Function.Surjective (MvPolynomial.aeval (R := K)
      (fun j : ChartVariables i => φ (chartCoordinate i j.1))) := by
    change Function.Surjective (MvPolynomial.aeval _).toRingHom
    rw [he]
    exact hφ.comp (polynomialChartEquiv (R := K) i).symm.surjective
  have hs := differentials_span_of_generators _ hp
  have hr : Set.range (fun j : ChartVariables i => D K A (-φ (chartCoordinate i j.1))) =
      -(Set.range (fun j : ChartVariables i => D K A (φ (chartCoordinate i j.1)))) := by
    ext x
    simp only [Set.mem_range, Set.mem_neg, map_neg, neg_eq_iff_eq_neg]
  rw [hr, Submodule.span_neg]
  exact hs

end
end MaximalSeshadri.ProjectiveBertini


end
end

end OAI
