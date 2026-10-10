import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.NormalizedMixed

namespace OAI

section
noncomputable section
                                              
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K ι κ : Type} [CommRing K] {X : Scheme}

lemma eval₂_surjective_subfamily {R : Type} [CommRing R] (k : K →+* R)
    (a : ι → R) (b : κ → R) (j : ι → κ) (hj : ∀ i, b (j i) = a i)
    (hs : Function.Surjective (MvPolynomial.eval₂Hom k a)) :
    Function.Surjective (MvPolynomial.eval₂Hom k b) := by
  intro r
  obtain ⟨p, hp⟩ := hs r
  refine ⟨rename j p, ?_⟩
  change eval₂ k b (rename j p) = r
  rw [eval₂_rename]
  have h : b ∘ j = a := funext hj
  change eval₂ k a p = r at hp
  simpa only [h] using hp

lemma sections_local_coordinates {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : ι → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (i : ι) (U : X.affineOpens) (hU : U.1 ≤ SectionOpens.isoOpen (s i))
    (hgen : Function.Surjective (eval₂Hom (U.1.ι.appTop.hom.comp k)
      (fun j => coefficient (sectionFrameOn (s i) U.1 hU)
        (restrictSection U.1.ι (s j))))) :
    ∃ φ : PolyChart (R := K) i →+* Γ(X, U.1), Function.Surjective φ ∧
      Spec.map (CommRingCat.ofHom φ) ≫
        Proj.awayι (PolyGrade K ι) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
          U.2.fromSpec ≫ sectionsMorphism k s hs := by
  let e := sectionFrameOn (s i) U.1 hU
  let k' := U.1.ι.appTop.hom.comp k
  let a (j : ι) := coefficient e (restrictSection U.1.ι (s j))
  have hai : a i = 1 := sectionFrameOn_normalized _ _ _
  let kU := U.1.topIso.hom.hom.comp k'
  let b (j : ι) := U.1.topIso.hom (a j)
  have hbi : b i = 1 := by simp [b, hai]
  have hsurj : Function.Surjective (eval₂Hom kU b) := by
    rw [show eval₂Hom kU b = U.1.topIso.hom.hom.comp (eval₂Hom k' a) from
      (coordinates_eval_natural U.1.topIso.hom.hom k' a).symm]
    exact U.1.topIso.commRingCatIsoToRingEquiv.surjective.comp hgen
  let φ : PolyChart (R := K) i →+* Γ(X, U.1) := evalAway (eval₂Hom kU b) (MvPolynomial.X i)
    (by simpa only [eval₂Hom_X', hbi] using (isUnit_one : IsUnit (1 : Γ(X, U.1))))
  refine ⟨φ, normalized_evalAway_surjective kU b i hbi hsurj, ?_⟩
  exact (affine_coordinates_factor U k' a i hai).symm.trans
    ((congrArg (fun morphism => U.2.isoSpec.inv ≫ morphism)
      (sectionsMorphism_on k s hs i U.1 hU).symm).trans
        (Category.assoc _ _ _).symm)

lemma quartic_generators {σ : Type} {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : Option σ → (O X ⟶ M)) (i : σ) (U : X.Opens)
    (hU : U ≤ SectionOpens.isoOpen (s (some i)))
    (hgen : Function.Surjective (eval₂Hom (U.ι.appTop.hom.comp k)
      (fun j => coefficient (sectionFrameOn (s (some i)) U hU)
        (restrictSection U.ι (s j))))) :
    Function.Surjective (eval₂Hom (U.ι.appTop.hom.comp k)
      (fun j : σ × σ × Option σ × Option σ =>
        coefficient (sectionFrameOn (powerSection (s (some i)) 4) U
          (hU.trans (sectionOpen_le_powerSection (s (some i)) 4)))
          (restrictSection U.ι (quarticSection (s (some j.1)) (s (some j.2.1))
            (s j.2.2.1) (s j.2.2.2))))) := by
  apply eval₂_surjective_subfamily _ _ _ (fun j => (i, i, some i, j)) _ hgen
  intro j
  rw [quarticSection_normalized _ _ _ _ _ U hU, sectionFrameOn_normalized]
  simp

end
end MaximalSeshadri.Projective

end


end
end

end OAI
