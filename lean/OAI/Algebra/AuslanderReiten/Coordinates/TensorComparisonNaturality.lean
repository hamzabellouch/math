import OAI.Algebra.AuslanderReiten.HomComplex.FullHomNaturality
import OAI.Algebra.AuslanderReiten.Triangular.TriangularComparison

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
namespace ArExplicit.TriangularInduction
universe u
variable {k R F G : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k Rᵐᵒᵖ F]
variable [AddCommGroup G] [Module k G] [Module R G] [Module Rᵐᵒᵖ G]
variable [SMulCommClass k R G] [SMulCommClass R Rᵐᵒᵖ G]
variable [IsScalarTower k Rᵐᵒᵖ G]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (a : F →ₗ[Rᵐᵒᵖ] G) (ha : ∀ (r : R) f, a (r • f) = r • a f)
variable {P : CochainComplex (ModuleCat.{u} R) ℤ}
variable (v : P ⟶ tensorCochain (k := k) (F := F) P) (n : ℤ)

theorem tensorComparison_natural
    (x : CohomologyClass P P n × CohomologyClass P P n) :
    fullHomPostcomp (BalancedTensor.complexMap (k := k) a ha P) n
      (tensorComparison v n x) =
    tensorComparison (v ≫ BalancedTensor.complexMap (k := k) a ha P) n x := by
  let t := BalancedTensor.complexMap (k := k) a ha P
  have ht : t = ((BalancedTensor.naturalMap (k := k) a ha).mapHomologicalComplex _).app P := rfl
  have hn (z : CohomologyClass P P n) :
      fullHomPostcomp t n (fullHomPrecomp v n
        (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)) P P n z)) =
      fullHomPrecomp (v ≫ t) n
        (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := G)) P P n z) := by
    rw [fullHomPostcomp_precomp, ht, mapFullHom_naturality, fullHomPrecomp_comp]
  change fullHomPostcomp t n (fullHomPostcomp v n x.2 + (n+1).negOnePow •
      fullHomPrecomp v n
        (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)) P P n x.1)) =
    fullHomPostcomp (v ≫ t) n x.2 + (n+1).negOnePow •
      fullHomPrecomp (v ≫ t) n
        (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := G)) P P n x.1)
  rw [map_add, Units.smul_def, map_zsmul, fullHomPostcomp_comp, hn]
  rfl

end ArExplicit.TriangularInduction

end

end OAI
