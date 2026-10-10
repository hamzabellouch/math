import OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationImmersion
import OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial AlgebraicGeometry CategoryTheory

universe u
variable {R ι σ : Type u} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

def projection (a : σ → ι →₀ ℕ) :
    Proj (imageGrade (R := R) a) ⟶ Spec (CommRingCat.of R) :=
  projectiveMonomialMap a ≫ polynomialProjectiveProjection R σ

instance projection_proper [Finite σ] (a : σ → ι →₀ ℕ) :
    IsProper (projection (R := R) a) := by
  have : IsProper (projectiveMonomialMap (R := R) a) := inferInstance
  exact MorphismProperty.comp_mem (@IsProper) _ _ inferInstance inferInstance

theorem projection_closed_projective_factorization [Finite σ] (a : σ → ι →₀ ℕ) :
    ∃ e : Proj (imageGrade (R := R) a) ⟶ Proj (homogeneousSubmodule σ R),
      IsClosedImmersion e ∧ e ≫ polynomialProjectiveProjection R σ = projection a :=
  ⟨projectiveMonomialMap a, inferInstance, rfl⟩

end PiExponent.WeightedCompactification

end

end OAI
