import OAI.NumberTheory.PiExponent.Cohomology.CurveEuler
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap

namespace OAI

namespace PiExponent.ProjectivePencilScalars
noncomputable section
open AlgebraicGeometry CategoryTheory

theorem projection_eq_structureMap (F : Type) [CommRing F] :
    polynomialProjectiveProjection F Bool = ProjectiveLine.structureMap F := by
  have hc : (polynomialGradeZeroEquiv F Bool).toRingHom =
      ProjectiveLine.constantsInDegreeZero F := by
    ext r
    rfl
  rw [polynomialProjectiveProjection, ProjectiveLine.structureMap, hc]

theorem scalars_comp_eq_structureScalars {F : Type} [CommRing F] {Y : Scheme.{0}}
    (f : Y ⟶ ProjectiveLine.projectiveLine F) :
    f.appTop.hom.comp (ProjectiveO1.scalars (R := F) (σ := Bool)) =
      (f ≫ ProjectiveLine.structureMap F).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom := by
  rw [ProjectiveO1.scalars, Scheme.Hom.comp_appTop, ← projection_eq_structureMap F]
  rfl

theorem scalars_comp_eq_baseScalars {Y : Scheme.{0}}
    (f : Y ⟶ ProjectiveLine.projectiveLine ℂ) :
    f.appTop.hom.comp (ProjectiveO1.scalars (R := ℂ) (σ := Bool)) =
      PiExponentSeshadri.Geometry.baseScalars (f ≫ ProjectiveLine.structureMap ℂ) :=
  scalars_comp_eq_structureScalars f

end
end PiExponent.ProjectivePencilScalars

end OAI
