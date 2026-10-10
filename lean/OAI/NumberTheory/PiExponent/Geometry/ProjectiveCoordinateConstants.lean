import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [CommRing K] (i : σ)
lemma evalAway_constants {R : Type} [CommRing R]
    (k : K →+* R) (a : σ → R) (hi : a i = 1) (r : K) :
    evalAway (eval₂Hom k a) (MvPolynomial.X i)
      (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
      (chartConstants i r) = k r := by
  have h := evalAway_mk_clear (eval₂Hom k a) (poly_X_mem (R := K) i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    0 (C r) (by simp)
  have he : chartConstants (R := K) i r = HomogeneousLocalization.Away.mk
      (PolyGrade K σ) (poly_X_mem i) 0 (C r) (by simp) := by
    apply HomogeneousLocalization.val_injective _
    simp [chartConstants, HomogeneousLocalization.fromZeroRingHom,
      HomogeneousLocalization.Away.val_mk]
    rfl
  rw [he]
  simpa only [pow_zero, mul_one, eval₂Hom_C] using h
lemma coordinatesMap_pullback_constant {Y : Scheme}
    (k : K →+* Γ(Y,⊤)) (a : σ → Γ(Y,⊤)) (hi : a i = 1)
    (g : Y ⟶ Spec (CommRingCat.of (PolyChart (R := K) i)))
    (heq : coordinatesMap Y k a i hi =
      g ≫ Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide))
    (r : K) :
    k r = ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv ≫
      g.appTop).hom (chartConstants i r) := by
  let F := evalAway (𝒜 := PolyGrade K σ) (eval₂Hom k a) (MvPolynomial.X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : Γ(Y,⊤))))
  have hfactor : Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom F) = g := by
    apply (cancel_mono (Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide))).1
    simpa only [coordinatesMap, fromUnitCoordinate, Category.assoc] using heq
  have hf := congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv ≫
    Scheme.Hom.appTop g) hfactor
  simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
    ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id] at hf
  have h := congrArg (fun g : CommRingCat.of (PolyChart (R := K) i) ⟶ _ =>
    g.hom (chartConstants i r)) hf
  change F (chartConstants i r) = _ at h
  rw [evalAway_constants i k a hi r] at h
  exact h
variable {X : Scheme} (M : X.Modules) (k : K →+* Γ(X,⊤))
    (s : σ → (PiExponentSeshadri.Frames.O X ⟶ M))
    (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
    (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)

lemma coordinateSectionRingEquiv_symm_constant (r : K) :
    (coordinateSectionRingEquiv M k s hc f hf i).symm (C r) =
      X.presheaf.map (homOfLE (show SectionOpens.isoOpen (s i) ≤ ⊤ from le_top)).op (k r) := by
  let U := SectionOpens.isoOpen (s i)
  let g := coordinateSectionChartIso M k s hc f hf i
  have h := coordinatesMap_pullback_constant i (U.ι.appTop.hom.comp k)
    (fun j => PiExponentSeshadri.Frames.coefficient (sectionFrame (s i))
      (PiExponentSeshadri.Frames.restrictSection U.ι (s j)))
    (sectionFrame_normalized (s i)) g.hom
    ((sectionsMorphism_local k s hc i).symm.trans
      (coordinateSectionChartIso_hom_away M k s hc f hf i).symm) r
  have hp : (polynomialChartEquiv (R := K) i).symm (C r) = chartConstants i r := by
    apply (polynomialChartEquiv i).injective
    rw [RingEquiv.apply_symm_apply]
    exact (chartToPoly_constants i r).symm
  change U.topIso.hom ((schemeIsoGammaEquiv g).symm
    ((polynomialChartEquiv i).symm (C r))) = _
  rw [hp]
  change U.ι.appTop (k r) = (schemeIsoGammaEquiv g).symm (chartConstants i r) at h
  rw [← h]
  simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  change (X.presheaf.map _ ≫ X.presheaf.map _) (k r) = _
  erw [← Functor.map_comp]
  rfl

lemma coordinateSectionRingEquiv_constant (r : K) :
    coordinateSectionRingEquiv M k s hc f hf i
      (X.presheaf.map (homOfLE (show SectionOpens.isoOpen (s i) ≤ ⊤ from le_top)).op (k r)) = C r := by
  rw [← coordinateSectionRingEquiv_symm_constant i M k s hc f hf r,
    RingEquiv.apply_symm_apply]

end

end Projective
end PiExponentSeshadri

end OAI
