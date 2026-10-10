import OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturalityCore

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] AlgebraicGeometry.StructureSheaf.openAlgebra
variable {R σ : Type*} [CommRing R] (i : σ)

private def relabeledOverlapEquiv {X : Scheme} {A : Type*} [CommRing A]
    (U V V' : X.Opens) (z z' : A)
    (e : Γ(X,U ⊓ V) ≃+* Localization.Away z) (hz : z = z') (hV : V = V') :
    Γ(X,U ⊓ V') ≃+* Localization.Away z' := by
  rw [hz, hV] at e
  exact e

private lemma relabeledOverlapEquiv_restrict {X : Scheme} {A : Type*} [CommRing A]
    (U V V' : X.Opens) (z z' : A)
    (e : Γ(X,U ⊓ V) ≃+* Localization.Away z) (hz : z = z') (hV : V = V')
    (a : Γ(X,U)) (p : A)
    (h : e (X.presheaf.map (homOfLE inf_le_left).op a) = algebraMap _ _ p) :
    relabeledOverlapEquiv U V V' z z' e hz hV
      (X.presheaf.map (homOfLE inf_le_left).op a) = algebraMap _ _ p := by
  subst z'
  subst V'
  exact h

lemma chartVariableOverlapRingEquiv_restrict (s : Finset (ChartVariables i))
    (p : MvPolynomial (ChartVariables i) R) :
    chartVariableOverlapRingEquiv i s
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) (polyToChart i p))) =
      algebraMap _ _ p := by
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
  change relabeledOverlapEquiv
    (Proj.basicOpen (PolyGrade R σ) (X i))
    ((s.image Subtype.val).inf fun j => Proj.basicOpen (PolyGrade R σ) (X j))
    (s.inf fun j => Proj.basicOpen (PolyGrade R σ) (X j.val)) _ _
    (chartFinitePolynomialRingEquiv i (s.image Subtype.val)) hprod
    (by rw [Finset.inf_image]; rfl) _ = _
  apply relabeledOverlapEquiv_restrict
  exact chartFinitePolynomialRingEquiv_restrict_poly i (s.image Subtype.val) p

lemma chartVariableOverlapRingEquiv_restrict_chart (s : Finset (ChartVariables i))
    (a : PolyChart (R := R) i) :
    chartVariableOverlapRingEquiv i s
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) a)) =
      algebraMap _ _ (chartToPoly i a) := by
  have h := chartVariableOverlapRingEquiv_restrict i s (chartToPoly i a)
  have hid := RingHom.congr_fun (polyToChart_comp_chartToPoly (R := R) i) a
  change polyToChart i (chartToPoly i a) = a at hid
  simpa only [hid] using h

@[simp] lemma chartVariableOverlapRingEquiv_restrict_coordinate
    (s : Finset (ChartVariables i)) (j : ChartVariables i) :
    chartVariableOverlapRingEquiv i s
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) (chartCoordinate i j.val))) =
      algebraMap _ _ (X (R := R) j) := by
  rw [chartVariableOverlapRingEquiv_restrict_chart]
  simp [chartToPoly_coordinate, j.property]

@[simp] lemma chartVariableOverlapRingEquiv_restrict_constant
    (s : Finset (ChartVariables i)) (r : R) :
    chartVariableOverlapRingEquiv i s
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) (chartConstants i r))) =
      algebraMap _ _ (C (σ := ChartVariables i) r) := by
  rw [chartVariableOverlapRingEquiv_restrict_chart, chartToPoly_constants]

lemma chartVariableOverlapRingEquiv_restriction_algebraMap
    (s t : Finset (ChartVariables i))
    (h : Proj.basicOpen (PolyGrade R σ) (X i) ⊓
        t.inf (fun j => Proj.basicOpen (PolyGrade R σ) (X j.val)) ≤
      Proj.basicOpen (PolyGrade R σ) (X i) ⊓
        s.inf (fun j => Proj.basicOpen (PolyGrade R σ) (X j.val)))
    (p : MvPolynomial (ChartVariables i) R) :
    chartVariableOverlapRingEquiv i t
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE h).op
        ((chartVariableOverlapRingEquiv i s).symm (algebraMap _ _ p))) =
      algebraMap _ _ p := by
  have hs : (chartVariableOverlapRingEquiv i s).symm (algebraMap _ _ p) =
      (Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) (polyToChart i p)) := by
    apply (chartVariableOverlapRingEquiv i s).injective
    rw [RingEquiv.apply_symm_apply]
    exact (chartVariableOverlapRingEquiv_restrict i s p).symm
  rw [hs]
  change chartVariableOverlapRingEquiv i t
    (((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op ≫
      (Proj (PolyGrade R σ)).presheaf.map (homOfLE h).op) _) = _
  rw [← Functor.map_comp]
  exact chartVariableOverlapRingEquiv_restrict i t p

end
end PiExponentSeshadri.Projective

end OAI
