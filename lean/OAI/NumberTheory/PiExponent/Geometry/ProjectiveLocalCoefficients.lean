import OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalSectionOrder
import OAI.NumberTheory.PiExponent.Polynomials.PullbackFrameCoefficient

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.Projective PiExponentSeshadri.LineBundleGluing

namespace PiExponent.ProjectiveLocalCoefficients


variable {R A σ : Type} [CommRing R] [CommRing A]
attribute [local instance] MvPolynomial.gradedAlgebra

def normalizedMap (k : R →+* A) (z : σ → A) (i : σ) (hi : z i = 1) :
    Spec (CommRingCat.of A) ⟶ ProjectiveO1.projectiveSpace R σ :=
  fromUnitCoordinate (eval₂Hom k z) (by decide) (poly_X_mem i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : A)))

theorem chart_inverse_ratio (i j : σ) :
    (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).inv.appTop
      (ProjectiveO1.chartRatios i j) =
        (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := R) i))).inv
          (chartCoordinate (R := R) i j) := by
  have h := ProjectiveO1.coordinateOpen_pullback (R := R) i
  have hc := congrArg (fun q => q ≫
    (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).inv.appTop) h
  simp only [Category.assoc, ← Scheme.Hom.comp_appTop,
    Iso.inv_hom_id, Scheme.Hom.id_appTop, Category.comp_id] at hc
  have hv := ConcreteCategory.congr_hom hc (chartCoordinate (R := R) i j)
  change (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := R) i))).inv
      (chartCoordinate (R := R) i j) =
    (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).inv.appTop
      ((ProjectiveO1.coordinateOpen i).topIso.inv
        (Proj.awayToSection (PolyGrade R σ) (X i) (chartCoordinate (R := R) i j))) at hv
  rw [ProjectiveO1.awayToSection_coordinate] at hv
  exact hv.symm

theorem exists_frame_coordinate_coefficients
    (k : R →+* A) (z : σ → A) (i : σ) (hi : z i = 1) :
    ∃ e : (Scheme.Modules.pullback (normalizedMap k z i hi)).obj
        (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf ≅ O (Spec (CommRingCat.of A)),
      ∀ j : σ,
        LocalSectionOrder.localCoefficient (A := A) e
          (pullbackSection (normalizedMap k z i hi) (ProjectiveO1.coordinateSection j)) = z j := by
  let U := ProjectiveO1.coordinateOpen (R := R) i
  let ev := evalAway (𝒜 := PolyGrade R σ) (eval₂Hom k z) (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : A)))
  let q := Spec.map (CommRingCat.ofHom ev)
  let g := q ≫ (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).inv
  have hf : normalizedMap k z i hi = g ≫ U.ι := by
    simp only [normalizedMap, fromUnitCoordinate, Proj.awayι, g, q, ev, U, Category.assoc]
  rw [hf]
  obtain ⟨e, he⟩ := PullbackFrameCoefficient.exists_frame_of_factors_through_open U g
    (openFrame ProjectiveO1.coordinateCocycle i U le_rfl)
  refine ⟨e, fun j => ?_⟩
  have hcoef : coefficient (openFrame ProjectiveO1.coordinateCocycle i U le_rfl)
      (restrictSection U.ι (ProjectiveO1.coordinateSection j)) =
        ProjectiveO1.chartRatios i j := by
    exact ProjectiveO1.coordinateSection_coefficient_eq i j U le_rfl
  have hj := he (ProjectiveO1.coordinateSection j)
  rw [hcoef] at hj
  change coefficient e (pullbackSection (g ≫ U.ι) (ProjectiveO1.coordinateSection j)) =
    q.appTop ((Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).inv.appTop
      (ProjectiveO1.chartRatios i j)) at hj
  rw [chart_inverse_ratio] at hj
  unfold LocalSectionOrder.localCoefficient
  erw [hj]
  change (q.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom)
    ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := R) i))).inv
      (chartCoordinate (R := R) i j)) = z j
  rw [Scheme.ΓSpecIso_naturality]
  change ev ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := R) i))).hom
    ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := R) i))).inv
      (chartCoordinate (R := R) i j))) = z j
  rw [Iso.inv_hom_id_apply]
  exact evalAway_coordinate i k z hi j

end PiExponent.ProjectiveLocalCoefficients

end

end OAI
