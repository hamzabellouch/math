import OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] AlgebraicGeometry.StructureSheaf.openAlgebra
variable {R σ : Type*} [CommRing R] (i : σ)

lemma away_chart_preimage_self :
    Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) ⁻¹ᵁ
      Proj.basicOpen (PolyGrade R σ) (X i) = ⊤ := by
  rw [← Proj.opensRange_awayι _ _ (poly_X_mem i) (by decide)]
  exact Scheme.Hom.preimage_opensRange _

lemma away_chart_appLE_top :
    (Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).appLE
      (Proj.basicOpen (PolyGrade R σ) (X i)) ⊤
      (by rw [away_chart_preimage_self]) =
    (Proj.basicOpen (PolyGrade R σ) (X i)).topIso.inv ≫
      (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).inv.appTop := by
  change ((Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).inv ≫
    (Proj.basicOpen (PolyGrade R σ) (X i)).ι).appLE _ _ _ = _
  rw [← Scheme.Hom.appLE_comp_appLE _ _ _ ⊤ ⊤
    (by simp) (by simp)]
  simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  congr 1

private lemma chartIso_pullback_top {X : Scheme} (U : X.Opens) (A : CommRingCat)
    (e : U.toScheme ≅ Spec A) (g : A ⟶ Γ(X,U))
    (he : e.hom.appTop = (Scheme.ΓSpecIso A).hom ≫ g ≫ U.topIso.inv) :
    g ≫ U.topIso.inv ≫ e.inv.appTop = (Scheme.ΓSpecIso A).inv := by
  apply (cancel_epi (Scheme.ΓSpecIso A).hom).mp
  rw [Iso.hom_inv_id]
  calc
    _ = e.hom.appTop ≫ e.inv.appTop := by rw [he]; simp only [Category.assoc]
    _ = 𝟙 _ := by rw [← Scheme.Hom.comp_appTop, e.inv_hom_id, Scheme.Hom.id_appTop]

lemma awayToSection_pullback_top :
    Proj.awayToSection (PolyGrade R σ) (X i) ≫
      (Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).appLE
        (Proj.basicOpen (PolyGrade R σ) (X i)) ⊤
        (by rw [away_chart_preimage_self]) =
      (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := R) i))).inv := by
  rw [away_chart_appLE_top]
  apply chartIso_pullback_top
  exact Proj.basicOpenToSpec_app_top (PolyGrade R σ) (X i)

local instance chartOpenAlgebra
    (V : (Spec (CommRingCat.of (PolyChart (R := R) i))).Opens) :
    Algebra (PolyChart (R := R) i) Γ(Spec (CommRingCat.of (PolyChart (R := R) i)),V) :=
  AlgebraicGeometry.StructureSheaf.openAlgebra _ _

lemma awayToSection_pullback_open (V : (Spec (CommRingCat.of (PolyChart (R := R) i))).Opens)
    (hV : V ≤ Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) ⁻¹ᵁ
      Proj.basicOpen (PolyGrade R σ) (X i)) :
    Proj.awayToSection (PolyGrade R σ) (X i) ≫
      (Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).appLE
        (Proj.basicOpen (PolyGrade R σ) (X i)) V hV =
      CommRingCat.ofHom (algebraMap (PolyChart (R := R) i) Γ(Spec (CommRingCat.of (PolyChart (R := R) i)),V)) := by
  change _ = (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := R) i))).inv ≫
    (Spec (CommRingCat.of (PolyChart (R := R) i))).presheaf.map (homOfLE le_top).op
  rw [← awayToSection_pullback_top (R := R) i, Category.assoc]
  congr 1

private def relabeledSectionIso {Y Z : Scheme} (f : Y ⟶ Z) [IsOpenImmersion f]
    (V U : Z.Opens) (W : Y.Opens) (hU : f.opensRange = U) (hW : f ⁻¹ᵁ V = W) :
    Γ(Y,W) ≅ Γ(Z,U ⊓ V) := by
  have e := IsOpenImmersion.ΓIso f V
  rw [hU, hW] at e
  exact e

private lemma relabeledSectionIso_inv {Y Z : Scheme} (f : Y ⟶ Z) [IsOpenImmersion f]
    (V U : Z.Opens) (W : Y.Opens) (hU : f.opensRange = U) (hW : f ⁻¹ᵁ V = W) :
    (relabeledSectionIso f V U W hU hW).inv = f.appLE (U ⊓ V) W (by
      rw [← hU, ← hW, ← f.image_preimage_eq_opensRange_inf, f.preimage_image_eq]) := by
  subst U
  subst W
  exact IsOpenImmersion.ΓIso_inv f V

lemma chartFiniteSectionRingEquiv_restrict (s : Finset σ) (a : PolyChart (R := R) i) :
    chartFiniteSectionRingEquiv i s
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) a)) =
      algebraMap _ _ a := by
  classical
  let z := ∏ j ∈ s, chartCoordinate (R := R) i j
  let : Algebra (PolyChart (R := R) i)
      Γ(Spec (CommRingCat.of (PolyChart (R := R) i)), PrimeSpectrum.basicOpen z) :=
    AlgebraicGeometry.StructureSheaf.openAlgebra _ _
  let : IsLocalization.Away z
      Γ(Spec (CommRingCat.of (PolyChart (R := R) i)), PrimeSpectrum.basicOpen z) :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen _ _
  let E := IsLocalization.algEquiv (Submonoid.powers z)
    Γ(Spec (CommRingCat.of (PolyChart (R := R) i)), PrimeSpectrum.basicOpen z)
    (Localization.Away z)
  change E ((relabeledSectionIso
    (Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide))
    (s.inf fun j => Proj.basicOpen (PolyGrade R σ) (X j))
    (Proj.basicOpen (PolyGrade R σ) (X i)) (PrimeSpectrum.basicOpen z)
    (Proj.opensRange_awayι _ _ (poly_X_mem i) (by decide))
    (coordinate_finset_preimage i s)).inv
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) a))) = _
  rw [← E.commutes a]
  apply congrArg E
  erw [relabeledSectionIso_inv]
  change (Proj.awayToSection (PolyGrade R σ) (X i) ≫
    (Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op ≫
    (Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).appLE _ _ _) a = _
  erw [Scheme.Hom.map_appLE]
  exact congrArg (fun f : CommRingCat.of (PolyChart (R := R) i) ⟶
    Γ(Spec (CommRingCat.of (PolyChart (R := R) i)), PrimeSpectrum.basicOpen z) => f a)
    (awayToSection_pullback_open i (PrimeSpectrum.basicOpen z) _)

attribute [local irreducible] chartFiniteSectionRingEquiv

lemma chartFinitePolynomialRingEquiv_restrict (s : Finset σ) (a : PolyChart (R := R) i) :
    chartFinitePolynomialRingEquiv i s
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) a)) =
      algebraMap _ _ (chartToPoly i a) := by
  rw [chartFinitePolynomialRingEquiv, RingEquiv.trans_apply, chartFiniteSectionRingEquiv_restrict]
  exact IsLocalization.ringEquivOfRingEquiv_eq _ _

lemma chartFinitePolynomialRingEquiv_restrict_poly (s : Finset σ)
    (p : MvPolynomial (ChartVariables i) R) :
    chartFinitePolynomialRingEquiv i s
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) (polyToChart i p))) =
      algebraMap _ _ p := by
  rw [chartFinitePolynomialRingEquiv_restrict]
  have h := RingHom.congr_fun (chartToPoly_comp_polyToChart (R := R) i) p
  change chartToPoly i (polyToChart i p) = p at h
  rw [h]

end
end PiExponentSeshadri.Projective

end OAI
