import OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedChartRingEvaluation
import OAI.NumberTheory.PiExponent.Polynomials.GlobalPolynomialCoefficientLaw

namespace OAI

namespace PiExponent.ProjectiveIntrinsicCoefficientLaw
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

structure CoordinateData (R σ : Type) [CommRing R] where
  scheme : Scheme.{0}
  sheaf : scheme.Modules
  sections : σ → (structureSheaf scheme ⟶ sheaf)
  scalars : R →+* Γ(scheme,⊤)
  cover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (sections i)) = ⊤
  projectiveIso : scheme ≅ Proj (PolyGrade R σ)
  projective_eq : sectionsMorphism scalars sections cover = projectiveIso.hom

namespace CoordinateData
variable {R σ : Type} [CommRing R] (D : CoordinateData R σ)

def chartOpen (z : σ) : D.scheme.Opens := PiExponentSeshadri.SectionOpens.isoOpen (D.sections z)

def Sections (n : ℕ) : Type := structureSheaf D.scheme ⟶ modulePow D.scheme D.sheaf n

def Frame (n : ℕ) (z : σ) : Type :=
  (modulePow D.scheme D.sheaf n).restrict (D.chartOpen z).ι ≅
    structureSheaf (D.chartOpen z).toScheme

def frame (n : ℕ) (z : σ) : D.Frame n z := coordinatePowerFrame (D.sections z) n

def ringEquiv (z : σ) : Γ(D.scheme,D.chartOpen z) ≃+* MvPolynomial (ChartVariables z) R :=
  coordinateSectionRingEquiv D.sheaf D.scalars D.sections D.cover D.projectiveIso D.projective_eq z

def polynomial (n : ℕ) (z : σ) : D.Sections n → MvPolynomial (ChartVariables z) R :=
  ProjectiveGlobalPolynomials.coordinateChartPolynomial D.sheaf D.sections D.scalars
    D.cover D.projectiveIso D.projective_eq n z

def Law (n : ℕ) (z : σ) : Prop :=
  GlobalPolynomialCoefficientLaw.CoefficientLaw (D.chartOpen z) (D.frame n z)
    (D.ringEquiv z) (D.polynomial n z)

theorem law (n : ℕ) (z : σ) : D.Law n z :=
  GlobalPolynomialCoefficientLaw.coordinate_law D.sheaf D.sections D.scalars
    D.cover D.projectiveIso D.projective_eq n z

end CoordinateData

attribute [local irreducible] ProjectiveO1.lineBundle ProjectiveO1.coordinateSection
  ProjectiveO1.scalars ProjectiveO1.coordinateCocycle sectionsMorphism
  CoordinateAtlas.morphism atlasOfFramedSections
  CoordinateData.chartOpen CoordinateData.Sections CoordinateData.Frame
  CoordinateData.frame CoordinateData.ringEquiv CoordinateData.polynomial CoordinateData.Law

variable {R σ : Type} [CommRing R]

def intrinsicData : CoordinateData R σ where
  scheme := ProjectiveO1.projectiveSpace R σ
  sheaf := (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf
  sections := ProjectiveO1.coordinateSection
  scalars := ProjectiveO1.scalars
  cover := ProjectiveO1.coordinateSection_cover
  projectiveIso := Iso.refl (ProjectiveO1.projectiveSpace R σ)
  projective_eq := ProjectiveO1.coordinate_sectionsMorphism_identity

def intrinsicBundle : LineBundle (intrinsicData (R := R) (σ := σ)).scheme :=
  ProjectiveO1.lineBundle (R := R) (σ := σ)

@[simp] theorem intrinsicBundle_sheaf :
    (intrinsicBundle (R := R) (σ := σ)).sheaf = (intrinsicData (R := R) (σ := σ)).sheaf := rfl

attribute [local semireducible] CoordinateData.Sections CoordinateData.chartOpen
  CoordinateData.polynomial CoordinateData.ringEquiv

theorem intrinsic_polynomial (n : ℕ) (z : σ) :
    (intrinsicData (R := R) (σ := σ)).polynomial n z =
      ProjectiveO1.globalSectionChartPolynomial (R := R) (σ := σ) n z := rfl

theorem intrinsic_ringEquiv (z : σ) :
    (intrinsicData (R := R) (σ := σ)).ringEquiv z =
      WeightedChartRingEvaluation.ambientRingEquiv (R := R) z := rfl

attribute [local irreducible] intrinsicData intrinsicBundle
  CoordinateData.Sections CoordinateData.chartOpen CoordinateData.polynomial CoordinateData.ringEquiv

theorem intrinsic_law (n : ℕ) (z : σ) : (intrinsicData (R := R) (σ := σ)).Law n z :=
  CoordinateData.law _ n z

end
end PiExponent.ProjectiveIntrinsicCoefficientLaw

end OAI
