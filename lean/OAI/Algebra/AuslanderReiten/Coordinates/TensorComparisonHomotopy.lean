import OAI.Algebra.AuslanderReiten.Coordinates.TensorComparisonNaturality
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomHomotopyMaps

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.TriangularInduction
universe u
variable {k R F : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {P : CochainComplex (ModuleCat.{u} R) ℤ}
variable {v w : P ⟶ tensorCochain (k := k) (F := F) P}

omit [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F] in
theorem tensorComparison_congr_homotopy
    (h : (HomotopyCategory.quotient _ _).map v = (HomotopyCategory.quotient _ _).map w)
    (n : ℤ) (x : CohomologyClass P P n × CohomologyClass P P n) :
    tensorComparison v n x = tensorComparison w n x := by
  change fullHomPostcomp v n x.2 + (n+1).negOnePow •
      fullHomPrecomp v n (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)) P P n x.1) =
    fullHomPostcomp w n x.2 + (n+1).negOnePow •
      fullHomPrecomp w n (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)) P P n x.1)
  rw [fullHomPostcomp_congr k n h, fullHomPrecomp_congr k n h]

end ArExplicit.TriangularInduction

end

end OAI
