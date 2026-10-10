import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveLine

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable (F : Type u) [CommRing F]

instance boolChartVariablesUnique (i : Bool) : Unique (ChartVariables i) where
  default := ⟨!i, by cases i <;> decide⟩
  uniq j := by
    apply Subtype.ext
    rcases j with ⟨j, hj⟩
    cases i <;> cases j <;> simp_all

def lineEvaluation (i : Bool) : MvPolynomial Bool F →+* Polynomial F :=
  MvPolynomial.eval₂Hom Polynomial.C (fun j => if j = i then 1 else Polynomial.X)

@[simp] theorem lineEvaluation_X (i j : Bool) :
    lineEvaluation F i (MvPolynomial.X j) = if j = i then 1 else Polynomial.X := by
  simp [lineEvaluation]

@[simp] theorem lineEvaluation_C (i : Bool) (r : F) :
    lineEvaluation F i (MvPolynomial.C r) = Polynomial.C r := by
  simp [lineEvaluation]

def chartRingEquiv (i : Bool) : PolyChart (R := F) i ≃+* Polynomial F :=
  (polynomialChartEquiv i).trans
    (MvPolynomial.uniqueAlgEquiv F (ChartVariables i)).toRingEquiv

lemma unique_dehomogenize (i : Bool) :
    (MvPolynomial.uniqueAlgEquiv F (ChartVariables i)).toRingHom.comp
      (dehomogenize (R := F) i) = lineEvaluation F i := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [dehomogenize, MvPolynomial.uniqueAlgEquiv_apply]
  · intro j
    by_cases h : j = i
    · subst j
      simp
    · simp [dehomogenize, h, MvPolynomial.uniqueAlgEquiv_apply]

lemma chartRingEquiv_eq_evalAway (i : Bool) :
    (chartRingEquiv F i).toRingHom =
      evalAway (𝒜 := PolyGrade F Bool) (lineEvaluation F i) (MvPolynomial.X i)
        (by simp) := by
  apply RingHom.ext
  intro x
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective _ (poly_X_mem (R := F) i) x
  change (MvPolynomial.uniqueAlgEquiv F (ChartVariables i))
    (chartToPoly i (Away.mk _ (poly_X_mem (R := F) i) n p hp)) = _
  rw [chartToPoly_mk]
  have h := RingHom.congr_fun (unique_dehomogenize F i) p
  change (MvPolynomial.uniqueAlgEquiv F (ChartVariables i)) (dehomogenize i p) = _ at h
  rw [h]
  symm
  simpa using evalAway_mk_clear (lineEvaluation F i) (poly_X_mem (R := F) i)
    (by simp) n p hp

def chartMap (i : Bool) : Spec (CommRingCat.of (Polynomial F)) ⟶ projectiveLine F :=
  Spec.map (CommRingCat.ofHom (chartRingEquiv F i).toRingHom) ≫
    Proj.awayι (PolyGrade F Bool) (MvPolynomial.X i) (poly_X_mem i) (by decide)

instance chartRingEquiv_isIso (i : Bool) :
    IsIso (CommRingCat.ofHom (chartRingEquiv F i).toRingHom) :=
  (chartRingEquiv F i).toCommRingCatIso.isIso_hom

instance chartMap_isOpenImmersion (i : Bool) : IsOpenImmersion (chartMap F i) := by
  unfold chartMap
  infer_instance

lemma chartMap_eq_fromUnitCoordinate (i : Bool) :
    chartMap F i = fromUnitCoordinate (𝒜 := PolyGrade F Bool)
      (lineEvaluation F i) (by decide) (poly_X_mem i) (by simp) := by
  unfold chartMap fromUnitCoordinate
  rw [chartRingEquiv_eq_evalAway]

@[simp] lemma chartMap_opensRange (i : Bool) :
    (chartMap F i).opensRange = Proj.basicOpen (PolyGrade F Bool) (MvPolynomial.X i) := by
  unfold chartMap
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

lemma chartMap_cover : (⨆ i : Bool, (chartMap F i).opensRange) = ⊤ := by
  simp only [chartMap_opensRange]
  exact standardChart_cover

lemma chartMap_preimage (i j : Bool) :
    chartMap F i ⁻¹ᵁ Proj.basicOpen (PolyGrade F Bool) (MvPolynomial.X j) =
      PrimeSpectrum.basicOpen (if j = i then (1 : Polynomial F) else Polynomial.X) := by
  rw [chartMap_eq_fromUnitCoordinate, fromUnitCoordinate_preimage _ (poly_X_mem i)
    (by simp) (by simp) (by decide) (poly_X_mem j), lineEvaluation_X]

lemma chartMap_preimage_other (i : Bool) :
    chartMap F i ⁻¹ᵁ (chartMap F (!i)).opensRange =
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial F) := by
  rw [chartMap_opensRange, chartMap_preimage]
  cases i <;> simp <;> rfl

@[reassoc] lemma chartMap_structureMap (i : Bool) :
    chartMap F i ≫ structureMap F = Spec.map (CommRingCat.ofHom Polynomial.C) := by
  unfold chartMap structureMap
  rw [Category.assoc, Proj.awayι_toSpecZero_assoc]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change (chartRingEquiv F i) (chartConstants i r) = Polynomial.C r
  change (MvPolynomial.uniqueAlgEquiv F (ChartVariables i))
    (chartToPoly i (chartConstants i r)) = _
  simp [MvPolynomial.uniqueAlgEquiv_apply]

end PiExponent.ProjectiveLine

end

end OAI
