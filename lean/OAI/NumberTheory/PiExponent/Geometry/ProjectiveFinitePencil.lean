import OAI.NumberTheory.PiExponent.Cohomology.PencilCohomology
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Morphism
import OAI.NumberTheory.PiExponent.Geometry.ProjectivePencilScalars
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback

namespace OAI

noncomputable section
namespace PiExponent.ProjectivePencil

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry PiExponentSeshadri.Projective


variable {K σ : Type} [CommRing K] {X : Scheme.{0}}

def lineBundle (f : X ⟶ ProjectiveO1.projectiveSpace K σ) : LineBundle X :=
  (ProjectiveO1.lineBundle (R := K) (σ := σ)).pullback f

def coordinateSection (f : X ⟶ ProjectiveO1.projectiveSpace K σ) (i : σ) :
    O X ⟶ (lineBundle f).sheaf :=
  pullbackSection f (ProjectiveO1.coordinateSection (R := K) i)

def scalars (f : X ⟶ ProjectiveO1.projectiveSpace K σ) : K →+* Γ(X,⊤) :=
  f.appTop.hom.comp (ProjectiveO1.scalars (R := K) (σ := σ))

theorem sections_cover (f : X ⟶ ProjectiveO1.projectiveSpace K σ) :
    (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection f i)) = ⊤ :=
  pullback_sections_cover ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover f

theorem sectionsMorphism_eq (f : X ⟶ ProjectiveO1.projectiveSpace K σ) :
    sectionsMorphism (scalars f) (coordinateSection f) (sections_cover f) = f := by
  have h := sectionsMorphism_pullback
    (M := (ProjectiveO1.lineBundle (R := K) (σ := σ)).sheaf)
    (ProjectiveO1.scalars (R := K) (σ := σ))
    ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover f
  rw [ProjectiveO1.coordinate_sectionsMorphism_identity, Category.comp_id] at h
  exact h.symm

instance sectionsMorphism_isFinite (f : X ⟶ ProjectiveO1.projectiveSpace K σ)
    [IsFinite f] : IsFinite (sectionsMorphism (scalars f) (coordinateSection f) (sections_cover f)) := by
  rw [sectionsMorphism_eq]
  infer_instance

end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {K : Type} [Field K] {X : Scheme.{0}}

theorem H0_finite [IsIntegral X]
    (f : X ⟶ ProjectiveO1.projectiveSpace K Bool) [IsFinite f]
    (hn : ¬ IsAffine X) (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 0) (scalars f)
    Module.Finite K (cohomology L.sheaf 0) :=
  finite_pencil_H0_finite (scalars f) (coordinateSection f) (sections_cover f) hn L

theorem H1_finite [IsNoetherian X]
    (f : X ⟶ ProjectiveO1.projectiveSpace K Bool) [IsFinite f] (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 1) (scalars f)
    Module.Finite K (cohomology L.sheaf 1) :=
  finite_pencil_H1_finite (scalars f) (coordinateSection f) (sections_cover f) L

end
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem scalars_eq_baseScalars
    (f : X ⟶ ProjectiveLine.projectiveLine ℂ) :
    scalars f = baseScalars (f ≫ ProjectiveLine.structureMap ℂ) :=
  ProjectivePencilScalars.scalars_comp_eq_baseScalars f

theorem H0_finite_complex [IsIntegral X]
    (f : X ⟶ ProjectiveLine.projectiveLine ℂ) [IsFinite f]
    (hn : ¬ IsAffine X) (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 0)
      (baseScalars (f ≫ ProjectiveLine.structureMap ℂ))
    Module.Finite ℂ (cohomology L.sheaf 0) := by
  rw [← scalars_eq_baseScalars f]
  exact H0_finite f hn L

theorem H1_finite_complex [IsNoetherian X]
    (f : X ⟶ ProjectiveLine.projectiveLine ℂ) [IsFinite f] (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 1)
      (baseScalars (f ≫ ProjectiveLine.structureMap ℂ))
    Module.Finite ℂ (cohomology L.sheaf 1) := by
  rw [← scalars_eq_baseScalars f]
  exact H1_finite f L

end PiExponent.ProjectivePencil

end

end OAI
