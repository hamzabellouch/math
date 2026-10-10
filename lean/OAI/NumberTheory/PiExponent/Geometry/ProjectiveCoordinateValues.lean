import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Projective
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [CommRing K] (i : σ)

lemma evalAway_coordinate {R : Type} [CommRing R]
    (k : K →+* R) (a : σ → R) (hi : a i = 1) (j : σ) :
    evalAway (eval₂Hom k a) (X i)
      (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
      (chartCoordinate (R := K) i j) = a j := by
  have h := evalAway_mk_clear (eval₂Hom k a) (poly_X_mem (R := K) i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    1 (X j) (by simpa using poly_X_mem (R := K) j)
  simpa only [chartCoordinate, eval₂Hom_X', hi, one_pow, mul_one] using h

lemma coordinatesMap_pullback_coordinate {Y : Scheme}
    (k : K →+* Γ(Y,⊤)) (a : σ → Γ(Y,⊤)) (hi : a i = 1)
    (g : Y ⟶ Spec (CommRingCat.of (PolyChart (R := K) i)))
    (heq : coordinatesMap Y k a i hi =
      g ≫ Proj.awayι (PolyGrade K σ) (X i) (poly_X_mem i) (by decide))
    (j : σ) :
    a j = ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv ≫
      g.appTop).hom (chartCoordinate (R := K) i j) := by
  let F := evalAway (𝒜 := PolyGrade K σ) (eval₂Hom k a) (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : Γ(Y,⊤))))
  have hfactor : Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom F) = g := by
    apply (cancel_mono (Proj.awayι (PolyGrade K σ) (X i) (poly_X_mem i) (by decide))).1
    simpa only [coordinatesMap, fromUnitCoordinate, Category.assoc] using heq
  have hf := congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv ≫
    Scheme.Hom.appTop g) hfactor
  simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
    ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id] at hf
  have h := congrArg (fun g : CommRingCat.of (PolyChart (R := K) i) ⟶ _ =>
    g.hom (chartCoordinate (R := K) i j)) hf
  change F (chartCoordinate (R := K) i j) = _ at h
  rw [evalAway_coordinate i k a hi j] at h
  exact h

lemma sectionFrame_coordinate {Y : Scheme} {M : Y.Modules}
    (k : K →+* Γ(Y,⊤)) (s : σ → (PiExponentSeshadri.Frames.O Y ⟶ M))
    (hc : (⨆ a, SectionOpens.isoOpen (s a)) = ⊤)
    (g : (SectionOpens.isoOpen (s i)).toScheme ⟶
      Spec (CommRingCat.of (PolyChart (R := K) i)))
    (hg : (SectionOpens.isoOpen (s i)).ι ≫ sectionsMorphism k s hc =
      g ≫ Proj.awayι (PolyGrade K σ) (X i) (poly_X_mem i) (by decide)) (j : σ) :
    PiExponentSeshadri.Frames.coefficient (sectionFrame (s i))
      (PiExponentSeshadri.Frames.restrictSection (SectionOpens.isoOpen (s i)).ι (s j)) =
    ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv ≫
      g.appTop).hom (chartCoordinate (R := K) i j) := by
  exact coordinatesMap_pullback_coordinate i
    ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
    (fun j => PiExponentSeshadri.Frames.coefficient (sectionFrame (s i))
      (PiExponentSeshadri.Frames.restrictSection (SectionOpens.isoOpen (s i)).ι (s j)))
    (sectionFrame_normalized (s i)) g
    ((sectionsMorphism_local k s hc i).symm.trans hg) j

end Projective

namespace Frames
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X Y Z W : Scheme}

lemma normalized_overlap_coefficients (φ : Y ⟶ X) (ψ : Z ⟶ X)
    (a : W ⟶ Y) (b : W ⟶ Z) [IsOpenImmersion φ] [IsOpenImmersion ψ]
    [IsOpenImmersion a] [IsOpenImmersion b] (h : a ≫ φ = b ≫ ψ)
    {M : X.Modules} (e : M.restrict φ ≅ O Y) (f : M.restrict ψ ≅ O Z)
    (si : O X ⟶ M) (hi : coefficient e (restrictSection φ si) = 1) :
    ∃ c : Γ(W,⊤)ˣ,
      (c : Γ(W,⊤)) = b.appTop (coefficient f (restrictSection ψ si)) ∧
      ∀ s : O X ⟶ M,
        b.appTop (coefficient f (restrictSection ψ s)) =
          (c : Γ(W,⊤)) * a.appTop (coefficient e (restrictSection φ s)) := by
  obtain ⟨c, hc⟩ := overlap_coefficients φ ψ a b h e f
  refine ⟨c, ?_, hc⟩
  have hci := hc si
  rw [hi, map_one, mul_one] at hci
  exact hci.symm

end Frames

end PiExponentSeshadri

end

end OAI
