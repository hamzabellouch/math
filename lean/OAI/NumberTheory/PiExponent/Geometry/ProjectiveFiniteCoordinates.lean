import OAI.NumberTheory.PiExponent.Cohomology.CohomologyFinite
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Identity
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceBasics

namespace OAI

noncomputable section

namespace PiExponent

namespace CohomologyFiniteness
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open GeometrySupport.ProjectiveCoordinateFinite
attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} {σ : Type} [Fintype σ] [Nonempty σ]

theorem finiteIndex_coordinateBundle_finite [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (s : σ → (structureSheaf X ⟶ L.sheaf))
    (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (f : X ≅ Proj (PolyGrade ℂ σ))
    (hf : sectionsMorphism (baseScalars p) s hc = f.hom)
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) : CohomologyFinite p M q := by
  let e := Fintype.equivFin σ
  let t : Fin (Fintype.card σ) → (structureSheaf X ⟶ L.sheaf) := fun i => s (e.symm i)
  have ht : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (t i)) = ⊤ :=
    (Equiv.iSup_comp (g := fun j => PiExponentSeshadri.SectionOpens.isoOpen (s j)) e.symm).trans hc
  exact CoherentProjectiveFinite.coherent_cohomology_finite_of_inverse_powers
    p L (Fintype.card σ) Fintype.card_pos t ht
    (fun i => GeometrySupport.ProjectiveTupleCharts.coordinateOpen_isAffine L.sheaf s (baseScalars p) hc f hf (e.symm i))
    (inversePower_cohomology_finite L s (baseScalars p) hc f hf) M q

end CohomologyFiniteness

namespace ProjectiveFiniteCoordinates
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open ProjectiveO1 CohomologyFiniteness
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] ProjectiveO1.lineBundle ProjectiveO1.coordinateCocycle
  ProjectiveO1.coordinateSection sectionsMorphism CoordinateAtlas.morphism atlasOfFramedSections
  CohomologyFinite
variable {X : Scheme.{0}} {σ : Type} [Finite σ] [Nonempty σ]

theorem projectiveSpace_cohomology_finite
    (M : (projectiveSpace ℂ σ).Modules) [M.IsFinitePresentation] (q : ℕ) :
    CohomologyFinite (polynomialProjectiveProjection ℂ σ) M q := by
  let : Fintype σ := Fintype.ofFinite σ
  have hid : sectionsMorphism
      (X := projectiveSpace ℂ σ) (K := ℂ) (σ := σ)
      (M := (lineBundle (R := ℂ) (σ := σ)).sheaf)
      (baseScalars (polynomialProjectiveProjection ℂ σ))
      (coordinateSection (R := ℂ) (σ := σ))
      (coordinateSection_cover (R := ℂ) (σ := σ)) =
      (Iso.refl (projectiveSpace ℂ σ)).hom :=
    coordinate_sectionsMorphism_identity (R := ℂ) (σ := σ)
  exact finiteIndex_coordinateBundle_finite (X := projectiveSpace ℂ σ)
    (polynomialProjectiveProjection ℂ σ)
    (lineBundle (R := ℂ) (σ := σ)) (coordinateSection (R := ℂ) (σ := σ))
    (coordinateSection_cover (R := ℂ) (σ := σ))
    (Iso.refl (projectiveSpace ℂ σ)) hid M q

theorem projectiveEmbedding_cohomology_finite
    (i : X ⟶ projectiveSpace ℂ σ) [IsClosedImmersion i]
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q)
      (baseScalars (i ≫ polynomialProjectiveProjection ℂ σ))
    FiniteDimensional ℂ (cohomology M q) := by
  exact finiteDimensional (i ≫ polynomialProjectiveProjection ℂ σ) M q
    (closedPushforward_finite i (polynomialProjectiveProjection ℂ σ) M q
      (projectiveSpace_cohomology_finite ((Scheme.Modules.pushforward i).obj M) q))

theorem projectiveOver_cohomology_finite (p : X ⟶ Spec (CommRingCat.of ℂ))
    (i : X ⟶ projectiveSpace ℂ σ) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ σ = p)
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := by
  subst p
  exact projectiveEmbedding_cohomology_finite i M q

end ProjectiveFiniteCoordinates

end PiExponent

end

end OAI
