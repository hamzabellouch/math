import OAI.Algebra.AuslanderReiten.Coordinates.TensorComparisonNaturality
import OAI.Algebra.AuslanderReiten.Coordinates.TensorComparisonHomotopy
import OAI.Algebra.AuslanderReiten.Coordinates.TensorComparisonScalar

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.TriangularInduction
universe u
variable {k R F G : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
variable [AddCommGroup G] [Module k G] [Module R G] [Module Rᵐᵒᵖ G]
variable [SMulCommClass k R G] [SMulCommClass R Rᵐᵒᵖ G]
variable [IsScalarTower k R G] [IsScalarTower k Rᵐᵒᵖ G] [SMulCommClass k Rᵐᵒᵖ G]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (a : F →ₗ[Rᵐᵒᵖ] G) (ha : ∀ (r : R) f, a (r • f) = r • a f)
variable {P : CochainComplex (ModuleCat.{u} R) ℤ}
variable (v : P ⟶ tensorCochain (k := k) (F := F) P)
variable (w : P ⟶ tensorCochain (k := k) (F := G) P)
variable (b : tensorCochain (k := k) (F := G) P ⟶ P)

omit [IsScalarTower k R F] [SMulCommClass k Rᵐᵒᵖ F]
    [IsScalarTower k R G] [SMulCommClass k Rᵐᵒᵖ G] in
theorem tensorComparison_projected_row
    (hprojection : (HomotopyCategory.quotient _ _).map
      (v ≫ BalancedTensor.complexMap (k := k) a ha P) =
        (HomotopyCategory.quotient _ _).map w)
    (hunit : (HomotopyCategory.quotient _ _).map (w ≫ b) = 𝟙 _)
    (n : ℤ) (c : k)
    (hscalar : ∀ z : CohomologyClass P P n,
      fullHomPostcomp b n (fullHomPrecomp w n
        (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := G)) P P n z)) = c • z)
    (x : CohomologyClass P P n × CohomologyClass P P n) :
    fullHomPostcomp b n
      (fullHomPostcomp (BalancedTensor.complexMap (k := k) a ha P) n
        (tensorComparison v n x)) = c • x.1 + x.2 := by
  rw [tensorComparison_natural]
  rw [tensorComparison_congr_homotopy (k := k) hprojection n x]
  exact tensorComparison_scalar_row w b hunit n c hscalar x

end ArExplicit.TriangularInduction

end

end OAI
