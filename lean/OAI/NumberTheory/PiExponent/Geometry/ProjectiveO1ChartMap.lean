import OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateValues
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveO1

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open HomogeneousLocalization PiExponentSeshadri.Projective

variable {R σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

def scalars : R →+* Γ(projectiveSpace R σ, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    (polynomialProjectiveProjection R σ).appTop).hom

theorem away_projection (i : σ) :
    Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) ≫
      polynomialProjectiveProjection R σ =
        Spec.map (CommRingCat.ofHom (chartConstants (R := R) i)) := by
  rw [polynomialProjectiveProjection, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  rfl

theorem coordinateOpen_projection (i : σ) :
    (coordinateOpen (R := R) i).ι ≫ polynomialProjectiveProjection R σ =
      (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).hom ≫
        Spec.map (CommRingCat.ofHom (chartConstants (R := R) i)) := by
  have h := congrArg (fun f =>
    (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).hom ≫ f)
    (away_projection (R := R) i)
  simpa only [Proj.awayι, Category.assoc, Iso.hom_inv_id_assoc] using h

theorem awayToSection_coordinate (i j : σ) :
    Proj.awayToSection (PolyGrade R σ) (X i) (chartCoordinate (R := R) i j) =
      coordinateRatio i j (coordinateOpen i) le_rfl := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  change (HomogeneousLocalization.mapId (PolyGrade R σ) _
    (chartCoordinate (R := R) i j)).val = _
  simp only [chartCoordinate, HomogeneousLocalization.mapId, HomogeneousLocalization.map,
    HomogeneousLocalization.Away.mk, pow_one]
  rfl

theorem scalarPullback_factorization {A : Type} [CommRing A]
    {X Y : Scheme} (π : X ⟶ Spec (CommRingCat.of R)) (ι : Y ⟶ X)
    (g : Y ⟶ Spec (CommRingCat.of A)) (f : R →+* A)
    (h : ι ≫ π = g ≫ Spec.map (CommRingCat.ofHom f)) :
    ι.appTop.hom.comp (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ π.appTop).hom) =
      (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g.appTop).hom).comp f := by
  have hh := congrArg (fun t : Y ⟶ Spec (CommRingCat.of R) =>
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ t.appTop) h
  simp only [Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc] at hh
  exact congrArg CommRingCat.Hom.hom hh

theorem coordinateOpen_pullback (i : σ) :
    (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := R) i))).inv ≫
      (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).hom.appTop =
    Proj.awayToSection (PolyGrade R σ) (X i) ≫
      (coordinateOpen (R := R) i).topIso.inv := by
  rw [Proj.basicOpenIsoSpec_hom]
  dsimp only [Scheme.Hom.appTop]
  rw [Proj.basicOpenToSpec_app_top, Iso.inv_hom_id_assoc]

theorem coordinateOpen_scalars (i : σ) :
    (coordinateOpen (R := R) i).ι.appTop.hom.comp (scalars (R := R) (σ := σ)) =
      ((Proj.awayToSection (PolyGrade R σ) (X i) ≫
        (coordinateOpen (R := R) i).topIso.inv).hom).comp (chartConstants i) := by
  have h := scalarPullback_factorization (polynomialProjectiveProjection R σ)
    (coordinateOpen (R := R) i).ι
    (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).hom
    (chartConstants i) (coordinateOpen_projection i)
  rw [coordinateOpen_pullback] at h
  exact h

def chartRatios (i : σ) (j : σ) : Γ((coordinateOpen (R := R) i).toScheme, ⊤) :=
  (coordinateOpen (R := R) i).topIso.inv (coordinateRatio i j (coordinateOpen i) le_rfl)

@[simp] theorem chartRatios_self (i : σ) : chartRatios (R := R) i i = 1 := by
  simp [chartRatios, coordinateRatio_self]

theorem evalAway_chartRatios (i : σ) :
    evalAway (eval₂Hom
      ((coordinateOpen (R := R) i).ι.appTop.hom.comp (scalars (R := R) (σ := σ)))
      (chartRatios i)) (X i)
      (by simpa only [eval₂Hom_X', chartRatios_self] using
        (isUnit_one : IsUnit (1 : Γ((coordinateOpen (R := R) i).toScheme, ⊤)))) =
    (Proj.awayToSection (PolyGrade R σ) (X i) ≫
      (coordinateOpen (R := R) i).topIso.inv).hom := by
  let k := (coordinateOpen (R := R) i).ι.appTop.hom.comp (scalars (R := R) (σ := σ))
  let F := evalAway (𝒜 := PolyGrade R σ) (eval₂Hom k (chartRatios i)) (X i)
    (by simpa only [eval₂Hom_X', chartRatios_self] using
      (isUnit_one : IsUnit (1 : Γ((coordinateOpen (R := R) i).toScheme, ⊤))))
  let Q := (Proj.awayToSection (PolyGrade R σ) (X i) ≫
    (coordinateOpen (R := R) i).topIso.inv).hom
  change F = Q
  have hh : F.comp (polyToChart i) = Q.comp (polyToChart i) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, polyToChart, eval₂Hom_C]
      rw [show F (chartConstants i r) = k r from
        evalAway_constants i k (chartRatios i) (chartRatios_self i) r]
      exact RingHom.congr_fun (coordinateOpen_scalars (R := R) i) r
    · intro j
      simp only [RingHom.comp_apply, polyToChart, eval₂Hom_X']
      rw [show F (chartCoordinate i j.val) = chartRatios i j.val from
        evalAway_coordinate i k (chartRatios i) (chartRatios_self i) j.val]
      exact congrArg (coordinateOpen (R := R) i).topIso.inv
        (awayToSection_coordinate i j.val).symm
  apply RingHom.ext
  intro a
  have ha := RingHom.congr_fun hh (chartToPoly i a)
  simpa only [RingHom.comp_apply,
    show polyToChart i (chartToPoly i a) = a from
      RingHom.congr_fun (polyToChart_comp_chartToPoly i) a] using ha

theorem coordinatesMap_chartRatios (i : σ) :
    coordinatesMap (coordinateOpen (R := R) i).toScheme
      ((coordinateOpen (R := R) i).ι.appTop.hom.comp (scalars (R := R) (σ := σ)))
      (chartRatios i) i (chartRatios_self i) = (coordinateOpen (R := R) i).ι := by
  unfold coordinatesMap fromUnitCoordinate
  rw [evalAway_chartRatios]
  change (coordinateOpen (R := R) i).toScheme.toSpecΓ ≫
    Spec.map (Proj.awayToSection (PolyGrade R σ) (X i) ≫
      (coordinateOpen (R := R) i).topIso.inv) ≫ _ = _
  simp only [Spec.map_comp, ← Category.assoc]
  change Proj.basicOpenToSpec (PolyGrade R σ) (X i) ≫ _ = _
  rw [← Proj.basicOpenIsoSpec_hom (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)]
  simp only [Proj.awayι, Iso.hom_inv_id_assoc]

end PiExponent.ProjectiveO1

end

end OAI
