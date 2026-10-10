import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra

lemma openImmersionSectionIso_restrict {Y Z : Scheme} (f : Y ⟶ Z)
    [IsOpenImmersion f] {U V : Z.Opens} (h : U ≤ V) :
    Z.presheaf.map (homOfLE (inf_le_inf_left f.opensRange h)).op ≫
      (IsOpenImmersion.ΓIso f U).inv =
    (IsOpenImmersion.ΓIso f V).inv ≫
      Y.presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ f ⁻¹ᵁ V from fun _ hx => h hx)).op := by
  simp only [IsOpenImmersion.ΓIso_inv, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

variable {R σ : Type*} [CommRing R] (i j : σ)
lemma coordinate_chart_preimage :
    Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) ⁻¹ᵁ
      Proj.basicOpen (PolyGrade R σ) (X j) =
      PrimeSpectrum.basicOpen (chartCoordinate (R := R) i j) := by
  rw [Proj.awayι_preimage_basicOpen _ _ (by decide) (poly_X_mem j) (by decide)]
  congr 1
  apply HomogeneousLocalization.val_injective _
  simp [HomogeneousLocalization.Away.isLocalizationElem, chartCoordinate,
    HomogeneousLocalization.Away.val_mk]

def chartPairSectionRingEquiv :
    Γ(Proj (PolyGrade R σ),
      Proj.basicOpen (PolyGrade R σ) (X i) ⊓ Proj.basicOpen (PolyGrade R σ) (X j)) ≃+*
      Localization.Away (chartCoordinate (R := R) i j) := by
  let f := Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)
  have e := IsOpenImmersion.ΓIso f (Proj.basicOpen (PolyGrade R σ) (X j))
  dsimp only [f] at e
  rw [Proj.opensRange_awayι, coordinate_chart_preimage] at e
  letI : Algebra (PolyChart (R := R) i)
      Γ(Spec (CommRingCat.of (PolyChart (R := R) i)),
        PrimeSpectrum.basicOpen (chartCoordinate (R := R) i j)) :=
    AlgebraicGeometry.StructureSheaf.openAlgebra _ _
  letI : IsLocalization.Away (chartCoordinate (R := R) i j)
      Γ(Spec (CommRingCat.of (PolyChart (R := R) i)),
        PrimeSpectrum.basicOpen (chartCoordinate (R := R) i j)) :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen _ _
  exact e.symm.commRingCatIsoToRingEquiv.trans
    (IsLocalization.algEquiv (Submonoid.powers (chartCoordinate (R := R) i j))
      Γ(Spec (CommRingCat.of (PolyChart (R := R) i)),
        PrimeSpectrum.basicOpen (chartCoordinate (R := R) i j))
      (Localization.Away (chartCoordinate (R := R) i j))).toRingEquiv

lemma coordinate_finset_preimage (s : Finset σ) :
    Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) ⁻¹ᵁ
      (s.inf fun j => Proj.basicOpen (PolyGrade R σ) (X j)) =
      PrimeSpectrum.basicOpen (∏ j ∈ s, chartCoordinate (R := R) i j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; rfl
  | @insert j s hjs ih =>
    simp only [Finset.inf_insert, Finset.prod_insert hjs, Scheme.Hom.preimage_inf, ih,
      coordinate_chart_preimage, PrimeSpectrum.basicOpen_mul]
    rfl

def chartFiniteSectionRingEquiv (s : Finset σ) :
    Γ(Proj (PolyGrade R σ),
      Proj.basicOpen (PolyGrade R σ) (X i) ⊓
        s.inf (fun j => Proj.basicOpen (PolyGrade R σ) (X j))) ≃+*
      Localization.Away (∏ j ∈ s, chartCoordinate (R := R) i j) := by
  let f := Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)
  have e := IsOpenImmersion.ΓIso f (s.inf fun j => Proj.basicOpen (PolyGrade R σ) (X j))
  dsimp only [f] at e
  rw [Proj.opensRange_awayι, coordinate_finset_preimage] at e
  let z := ∏ j ∈ s, chartCoordinate (R := R) i j
  letI : Algebra (PolyChart (R := R) i)
      Γ(Spec (CommRingCat.of (PolyChart (R := R) i)), PrimeSpectrum.basicOpen z) :=
    AlgebraicGeometry.StructureSheaf.openAlgebra _ _
  letI : IsLocalization.Away z
      Γ(Spec (CommRingCat.of (PolyChart (R := R) i)), PrimeSpectrum.basicOpen z) :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen _ _
  exact e.symm.commRingCatIsoToRingEquiv.trans
    (IsLocalization.algEquiv (Submonoid.powers z)
      Γ(Spec (CommRingCat.of (PolyChart (R := R) i)), PrimeSpectrum.basicOpen z)
      (Localization.Away z)).toRingEquiv

def chartFinitePolynomialRingEquiv (s : Finset σ) :
    Γ(Proj (PolyGrade R σ),
      Proj.basicOpen (PolyGrade R σ) (X i) ⊓
        s.inf (fun j => Proj.basicOpen (PolyGrade R σ) (X j))) ≃+*
      Localization.Away (∏ j ∈ s, chartToPoly (R := R) i (chartCoordinate i j)) :=
  (chartFiniteSectionRingEquiv i s).trans
    (IsLocalization.ringEquivOfRingEquiv
      (M := Submonoid.powers (∏ j ∈ s, chartCoordinate (R := R) i j))
      (T := Submonoid.powers (∏ j ∈ s, chartToPoly (R := R) i (chartCoordinate i j)))
      (Localization.Away (∏ j ∈ s, chartCoordinate (R := R) i j))
      (Localization.Away (∏ j ∈ s, chartToPoly (R := R) i (chartCoordinate i j)))
      (polynomialChartEquiv i) (by
      rw [Submonoid.map_powers]
      congr 1
      exact map_prod (polynomialChartEquiv i) _ _))

def chartVariableOverlapRingEquiv (s : Finset (ChartVariables i)) :
    Γ(Proj (PolyGrade R σ),
      Proj.basicOpen (PolyGrade R σ) (X i) ⊓
        s.inf (fun j => Proj.basicOpen (PolyGrade R σ) (X j.val))) ≃+*
      Localization.Away (∏ j ∈ s, (X j : MvPolynomial (ChartVariables i) R)) := by
  classical
  have hprod : (∏ j ∈ s.image Subtype.val,
      chartToPoly (R := R) i (chartCoordinate i j)) =
      ∏ j ∈ s, (X j : MvPolynomial (ChartVariables i) R) := by
    rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro j hj
      simp [chartToPoly_coordinate, j.property]
    · intro a ha b hb hab
      exact Subtype.ext hab
  have e := chartFinitePolynomialRingEquiv (R := R) i (s.image Subtype.val)
  rw [hprod, Finset.inf_image] at e
  exact e

end
end PiExponentSeshadri.Projective

end OAI
