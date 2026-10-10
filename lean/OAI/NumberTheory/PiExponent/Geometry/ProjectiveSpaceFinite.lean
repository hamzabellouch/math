import OAI.NumberTheory.PiExponent.Cohomology.CohomologyFinite
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Identity
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceBasics

namespace OAI

namespace PiExponent.ProjectiveSpaceFinite
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open ProjectiveO1 CohomologyFiniteness
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] ProjectiveO1.lineBundle ProjectiveO1.coordinateCocycle
  ProjectiveO1.coordinateSection sectionsMorphism CoordinateAtlas.morphism atlasOfFramedSections
  CohomologyFinite
variable {X : Scheme.{0}}

theorem projectiveSpace_cohomology_finite (r : ℕ)
    (M : (projectiveSpace ℂ (Fin (r+1))).Modules) [M.IsFinitePresentation] (q : ℕ) :
    CohomologyFinite (polynomialProjectiveProjection ℂ (Fin (r+1))) M q := by
  have hid : sectionsMorphism
      (X := projectiveSpace ℂ (Fin (r+1))) (K := ℂ) (σ := Fin (r+1))
      (M := (lineBundle (R := ℂ) (σ := Fin (r+1))).sheaf)
      (baseScalars (polynomialProjectiveProjection ℂ (Fin (r+1))))
      (coordinateSection (R := ℂ) (σ := Fin (r+1))) coordinateSection_cover =
      (Iso.refl (projectiveSpace ℂ (Fin (r+1)))).hom := by
    change sectionsMorphism
      (M := (lineBundle (R := ℂ) (σ := Fin (r+1))).sheaf)
      (baseScalars (polynomialProjectiveProjection ℂ (Fin (r+1))))
      (coordinateSection (R := ℂ) (σ := Fin (r+1)))
      (coordinateSection_cover (R := ℂ) (σ := Fin (r+1))) =
        𝟙 (projectiveSpace ℂ (Fin (r+1)))
    exact coordinate_sectionsMorphism_identity (R := ℂ) (σ := Fin (r+1))
  exact coordinateBundle_finite (X := projectiveSpace ℂ (Fin (r+1)))
    (polynomialProjectiveProjection ℂ (Fin (r+1)))
    (lineBundle (R := ℂ) (σ := Fin (r+1))) (r+1) (Nat.succ_pos r)
    (coordinateSection (R := ℂ) (σ := Fin (r+1)))
    (coordinateSection_cover (R := ℂ) (σ := Fin (r+1)))
    (Iso.refl (projectiveSpace ℂ (Fin (r+1)))) hid M q

theorem projectiveEmbedding_cohomology_finite (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q)
      (baseScalars (i ≫ polynomialProjectiveProjection ℂ (Fin (r+1))))
    FiniteDimensional ℂ (cohomology M q) := by
  exact finiteDimensional (i ≫ polynomialProjectiveProjection ℂ (Fin (r+1))) M q
    (closedPushforward_finite i (polynomialProjectiveProjection ℂ (Fin (r+1))) M q
      (projectiveSpace_cohomology_finite r ((Scheme.Modules.pushforward i).obj M) q))

theorem projectiveOver_cohomology_finite (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := by
  subst p
  exact projectiveEmbedding_cohomology_finite r i M q

end
end PiExponent.ProjectiveSpaceFinite

end OAI
