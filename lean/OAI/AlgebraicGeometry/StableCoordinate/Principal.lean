import OAI.AlgebraicGeometry.StableCoordinate.Degree
import OAI.AlgebraicGeometry.StableCoordinate.GeometricInterpretation
import OAI.AlgebraicGeometry.StableCoordinate.Stabilization
import OAI.AlgebraicGeometry.StableCoordinate.StabilizationEmbedding
import OAI.AlgebraicGeometry.StableCoordinate.AllFibers
import OAI.AlgebraicGeometry.StableCoordinate.NonCoordinate

namespace OAI

/-!
# The stable noncoordinate polynomial and its fibers

The degree-five polynomial becomes a coordinate after adjoining one variable
but is not a coordinate in four variables. Every complex fiber is affine
three-space and has a nonrectifiable embedding in affine four-space.
-/

namespace StableCoordinate

/-- The exact polynomial has degree five, is one-stable, and is not a
coordinate in its original four-variable polynomial algebra. -/
theorem polynomial_package : PolynomialPackage :=
  ⟨f_totalDegree, f_isOneStableCoordinate, f_not_coordinate⟩

/-- Every complex fiber is affine three-space and its embedding in affine
four-space is nonrectifiable. -/
theorem fiber_package : FiberPackage :=
  fiberPackage_of_noncoordinate f_not_coordinate

/-- Both complete principal groups, with every required quantifier. -/
theorem principal_package : PrincipalPackage :=
  ⟨polynomial_package, fiber_package⟩

/-- Literal polynomial-extension form of the unrestricted stabilization. -/
theorem f_is_coordinate_in_polynomial_extension :
    ∃ φ : Polynomial (R 4) ≃ₐ[ℂ] Polynomial (R 4),
      φ (Polynomial.C f) = Polynomial.C (MvPolynomial.X 0) :=
  (isOneStableCoordinate_iff_polynomial f).mp f_isOneStableCoordinate

/-- The exact example disproves the stable-coordinate statement for four
original variables and one independent added variable over `ℂ`. -/
theorem stable_coordinate_conjecture_four_false :
    ¬ (∀ g : R 4, IsOneStableCoordinate g →
      IsCoordinate (by decide : 0 < 4) g) := by
  intro h
  exact f_not_coordinate (h f f_isOneStableCoordinate)

/-- The dimension-four Abhyankar–Sathaye statement over `ℂ` fails for this
exact polynomial.  Its zero fiber already supplies the required counterexample;
the stronger all-fiber statement is `fiber_package`. -/
theorem abhyankar_sathaye_statement_four_false :
    ¬ (∀ g : R 4,
      Nonempty ((R 4 ⧸ Ideal.span ({g} : Set (R 4))) ≃ₐ[ℂ] R 3) →
      IsCoordinate (by decide : 0 < 4) g) := by
  intro h
  apply f_not_coordinate
  apply h f
  have hI : fiberIdeal 0 = Ideal.span ({f} : Set (R 4)) := by
    unfold fiberIdeal
    rw [MvPolynomial.C_0, sub_zero]
  exact ⟨(Ideal.quotientEquivAlgOfEq ℂ hI.symm).trans (exactFiberEquiv 0)⟩

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

/-- The all-fiber result as actual schemes over `Spec ℂ`, with the actual
closed hypersurface immersion and obstruction to every base-preserving ambient
scheme automorphism.  This is not merely a statement about sets of points. -/
theorem all_fibers_geometric_conclusion :
    ∀ t : ℂ,
      Nonempty (AffineGeometry.algebraSpec ℂ (FiberRing t) ≅
        Over.mk (AffineSpace (Fin 3) (Spec (CommRingCat.of ℂ)) ↘
          Spec (CommRingCat.of ℂ))) ∧
      IsClosedImmersion (GeometricInterpretation.fiberEmbedding t) ∧
      ¬ GeometricInterpretation.IsSchemeRectifiableFiber t :=
  GeometricInterpretation.fiberPackage_gives_geometric_conclusion fiber_package

end StableCoordinate

end OAI
