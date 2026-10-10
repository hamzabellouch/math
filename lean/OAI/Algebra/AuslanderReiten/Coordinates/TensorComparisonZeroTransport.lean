import OAI.Algebra.AuslanderReiten.Coordinates.TensorComparisonZero

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.TriangularInduction
universe u
variable {k R F : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {P : CochainComplex (ModuleCat.{u} R) ℤ}
variable (v : P ⟶ tensorCochain (k := k) (F := F) P)
variable {V : Type u} [AddCommGroup V] [Module k V]

theorem tensorComparison_zero_surjective_of_equiv
    (E : CohomologyClass P (tensorCochain (k := k) (F := F) P) 0 ≃ₗ[k] V)
    (g : V) (he : E (CohomologyClass.mk (Cocycle.ofHom v)) = g)
    (hg : ∀ z, ∃ a : k, a • g = z) :
    Function.Surjective (tensorComparison v 0) := by
  apply tensorComparison_zero_surjective
  intro z
  obtain ⟨a,ha⟩ := hg (E z)
  refine ⟨a,E.injective ?_⟩
  rw [map_smul, he, ha]

end ArExplicit.TriangularInduction

end

end OAI
