import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.HyperplaneIdeal
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionChart

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.IdealPullback
noncomputable section
open AlgebraicGeometry CategoryTheory
variable {X : Scheme} {R : Type} [CommRing R]

lemma specIdeal_injective : Function.Injective (specIdeal (R := R)) := by
  intro I J h
  have hh := congrArg (fun A => A.ideal ⟨⊤, isAffineOpen_top (Spec (.of R))⟩) h
  simp only [specIdeal_top] at hh
  have hh' := congrArg (Ideal.map (Scheme.ΓSpecIso (.of R)).hom.hom) hh
  have he : (Scheme.ΓSpecIso (.of R)).hom.hom.comp
      (Scheme.ΓSpecIso (.of R)).inv.hom = RingHom.id R := by
    exact congrArg CommRingCat.Hom.hom (Iso.inv_hom_id (Scheme.ΓSpecIso (.of R)))
  simpa only [Ideal.map_map, he, Ideal.map_id] using hh'

lemma comap_fromSpec (I : X.IdealSheafData) (U : X.affineOpens) :
    I.comap U.2.fromSpec = specIdeal (I.ideal U) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [← U.2.isoSpec_inv_ι, Scheme.IdealSheafData.comap_comp, comap_top,
    comap_ι_top, U.2.isoSpec_inv_appTop, specIdeal_top]
  rw [Ideal.map_map]
  congr 1
  simp only [← CommRingCat.hom_comp, Iso.inv_hom_id_assoc]
  rfl

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.IdealPullback
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

lemma ambientHyperplane_comap_equation
    (h : X ⟶ Proj (PolyGrade K σ)) (v : σ → K) (U : X.affineOpens) (i : σ)
    (φ : PolyChart (R := K) i →+* Γ(X, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        U.2.fromSpec ≫ h) :
    ((ambientHyperplane v).comap h).ideal U =
      Ideal.span {∑ j, φ (chartConstants i (v j)) * φ (chartCoordinate i j)} := by
  apply specIdeal_injective
  rw [← comap_fromSpec, ← Scheme.IdealSheafData.comap_comp, ← hφ,
    Scheme.IdealSheafData.comap_comp, ambientHyperplane_chart, specIdeal_comap,
    Ideal.map_span, Set.image_singleton]
  simp only [map_sum, map_mul]

lemma section_hyperplane_equation {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → K) (U : X.affineOpens) (i : σ)
    (φ : PolyChart (R := K) i →+* Γ(X, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        U.2.fromSpec ≫ sectionsMorphism k s hs) :
    ∃ e : M.restrict U.1.ι ≅ O U.1.toScheme,
      ((ambientHyperplane v).comap (sectionsMorphism k s hs)).ideal U =
        Ideal.span {U.1.topIso.hom (coefficient e
          (restrictSection U.1.ι (sectionCombination k s v)))} := by
  obtain ⟨e, he⟩ := sectionsMorphism_affine_equation k s hs U i φ hφ
  exact ⟨e, (ambientHyperplane_comap_equation _ v U i φ hφ).trans
    (congrArg (fun f => Ideal.span ({f} : Set Γ(X, U.1))) (he v).symm)⟩

end
end MaximalSeshadri.Projective
end


end
end

end OAI
