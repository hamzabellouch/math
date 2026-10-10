import OAI.NumberTheory.PiExponent.Approximation.WeightedAffineParametrization
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Identity

namespace OAI

namespace PiExponent.WeightedChartRingEvaluation
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponentSeshadri.Frames PiExponentSeshadri
open PiExponent.WeightedCompactification
attribute [local instance] MvPolynomial.gradedAlgebra

section Generic
variable {X : Scheme} {K σ A : Type} [CommRing K] [CommRing A]
variable (M : X.Modules) (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ M))
  (hc : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
  (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc = f.hom)
  (i : σ) (v : PolyChart (R := K) i →+* A)
  (g : Spec (CommRingCat.of A) ⟶ (SectionOpens.isoOpen (s i)).toScheme)
  (hg : g ≫ (coordinateSectionChartIso M k s hc f hf i).hom =
    Spec.map (CommRingCat.ofHom v))

include hg

theorem chart_pullback (q : MvPolynomial (ChartVariables i) K) :
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (g.appTop ((SectionOpens.isoOpen (s i)).topIso.inv
        ((coordinateSectionRingEquiv M k s hc f hf i).symm q))) = v (polyToChart i q) := by
  let U := SectionOpens.isoOpen (s i)
  let e := coordinateSectionChartIso M k s hc f hf i
  have hcancel (x : Γ(U.toScheme, ⊤)) : U.topIso.inv (U.topIso.hom x) = x :=
    CategoryTheory.congr_fun U.topIso.hom_inv_id x
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (g.appTop (U.topIso.inv (U.topIso.hom
      (e.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv
        (polyToChart i q)))))) = _
  rw [hcancel]
  change (e.hom.appTop ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom)
    ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv (polyToChart i q)) = _
  rw [← Scheme.Hom.comp_appTop_assoc, hg, Scheme.ΓSpecIso_naturality]
  change v ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).hom
    ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv (polyToChart i q))) = _
  exact congrArg v (CategoryTheory.congr_fun
    (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv_hom_id _)
end Generic

variable {R ι σ : Type} [CommRing R]

theorem evalAway_polyToChart (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (q : MvPolynomial (ChartVariables z) R) :
    evalAway (affineMonomialMap (R := R) a) (X z)
      (by simp [affineMonomialMap, hz])
      (polyToChart z q) =
      eval₂Hom C (fun j : ChartVariables z => monomial (a j.val) (1 : R)) q := by
  have ha : monomial (a z) (1 : R) = (1 : MvPolynomial ι R) := by simp [hz]
  have he :
      (evalAway (affineMonomialMap (R := R) a) (X z)
        (by simp [affineMonomialMap, hz])).comp (polyToChart z) =
      eval₂Hom C (fun j : ChartVariables z => monomial (a j.val) (1 : R)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, polyToChart, eval₂Hom_C]
      exact evalAway_constants z C (fun j => monomial (a j) (1 : R)) ha r
    · intro j
      simp only [RingHom.comp_apply, polyToChart, eval₂Hom_X']
      exact evalAway_coordinate z C (fun j => monomial (a j) (1 : R)) ha j.val
  exact RingHom.congr_fun he q

abbrev ambientOpen (z : σ) : (ProjectiveO1.projectiveSpace R σ).Opens :=
  SectionOpens.isoOpen (ProjectiveO1.coordinateSection (R := R) z)

def ambientRingEquiv (z : σ) :
    Γ(ProjectiveO1.projectiveSpace R σ, ambientOpen (R := R) z) ≃+*
      MvPolynomial (ChartVariables z) R :=
  coordinateSectionRingEquiv (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf
    ProjectiveO1.scalars ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover
    (Iso.refl _) ProjectiveO1.coordinate_sectionsMorphism_identity z

def chartFactor (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (_coordinate : ι → σ) (_hcoordinate : ∀ i, a (_coordinate i) = Finsupp.single i 1) :
    Spec (CommRingCat.of (MvPolynomial ι R)) ⟶ (ambientOpen (R := R) z).toScheme :=
  Spec.map (CommRingCat.ofHom
    (evalAway (𝒜 := PolyGrade R σ) (affineMonomialMap (R := R) a) (X z)
      (by simp [affineMonomialMap, hz]))) ≫
    (coordinateSectionChartIso (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf
      ProjectiveO1.scalars ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover
      (Iso.refl _) ProjectiveO1.coordinate_sectionsMorphism_identity z).inv

theorem chartFactor_comp (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    affineChartMap (R := R) a z hz coordinate hcoordinate ≫ projectiveMonomialMap a =
      chartFactor a z hz coordinate hcoordinate ≫ (ambientOpen (R := R) z).ι := by
  have he := coordinateSectionChartIso_hom_away
    (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf
    ProjectiveO1.scalars ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover
    (Iso.refl _) ProjectiveO1.coordinate_sectionsMorphism_identity z
  rw [ProjectiveO1.coordinate_sectionsMorphism_identity, Category.comp_id] at he
  rw [affineChartMap_comp_projectiveMonomialMap]
  unfold chartFactor fromUnitCoordinate
  rw [← he]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

theorem ambient_chart_pullback (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (g : Spec (CommRingCat.of (MvPolynomial ι R)) ⟶ (ambientOpen (R := R) z).toScheme)
    (hg : g ≫ (ambientOpen (R := R) z).ι =
      affineChartMap a z hz coordinate hcoordinate ≫ projectiveMonomialMap a)
    (q : MvPolynomial (ChartVariables z) R) :
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι R))).hom
      (g.appTop ((ambientOpen (R := R) z).topIso.inv ((ambientRingEquiv z).symm q))) =
      eval₂Hom C (fun j : ChartVariables z => monomial (a j.val) (1 : R)) q := by
  let v : PolyChart (R := R) z →+* MvPolynomial ι R := evalAway (affineMonomialMap (R := R) a) (X z)
    (show IsUnit (affineMonomialMap (R := R) a (X z)) from by
      simp [affineMonomialMap, hz])
  have hfactor : g ≫
      (coordinateSectionChartIso (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf
        ProjectiveO1.scalars ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover
        (Iso.refl _) ProjectiveO1.coordinate_sectionsMorphism_identity z).hom =
      Spec.map (CommRingCat.ofHom v) := by
    apply (cancel_mono (Proj.awayι (PolyGrade R σ) (X z) (poly_X_mem z) (by decide))).mp
    rw [Category.assoc, coordinateSectionChartIso_hom_away,
      ProjectiveO1.coordinate_sectionsMorphism_identity, Category.comp_id, hg,
      affineChartMap_comp_projectiveMonomialMap]
    rfl
  exact (chart_pullback (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf
    ProjectiveO1.scalars ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover
    (Iso.refl _) ProjectiveO1.coordinate_sectionsMorphism_identity z v g hfactor q).trans
      (evalAway_polyToChart a z hz q)

theorem chartFactor_pullback (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (q : MvPolynomial (ChartVariables z) R) :
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι R))).hom
      ((chartFactor a z hz coordinate hcoordinate).appTop
        ((ambientOpen (R := R) z).topIso.inv ((ambientRingEquiv z).symm q))) =
      eval₂Hom C (fun j : ChartVariables z => monomial (a j.val) (1 : R)) q :=
  ambient_chart_pullback a z hz coordinate hcoordinate
    (chartFactor a z hz coordinate hcoordinate) (chartFactor_comp a z hz coordinate hcoordinate).symm q

end
end PiExponent.WeightedChartRingEvaluation

end OAI
