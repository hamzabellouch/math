import OAI.Algebra.AuslanderReiten.Triangular.TriangularComparison
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomHomotopyMaps
import OAI.Algebra.AuslanderReiten.Homology.TriangleConnectingProduct
import OAI.Algebra.AuslanderReiten.Coordinates.TwoTwistLinear

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.TriangularInduction
universe u
variable {k R F : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {P : CochainComplex (ModuleCat.{u} R) ℤ}
variable (v : P ⟶ tensorCochain (k := k) (F := F) P)

omit [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F] in
theorem tensorComparison_scalar_row (b : tensorCochain (k := k) (F := F) P ⟶ P)
    (hunit : (HomotopyCategory.quotient (ModuleCat.{u} R) _).map (v ≫ b) = 𝟙 _)
    (n : ℤ) (c : k)
    (hscalar : ∀ z : CohomologyClass P P n,
      fullHomPostcomp b n (fullHomPrecomp v n
        (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)) P P n z)) = c • z)
    (x : CohomologyClass P P n × CohomologyClass P P n) :
    fullHomPostcomp b n (tensorComparison v n x) = c • x.1 + x.2 := by
  change fullHomPostcomp b n (fullHomPostcomp v n x.2 + (n+1).negOnePow •
    fullHomPrecomp v n
      (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)) P P n x.1)) = _
  rw [map_add, Units.smul_def, map_zsmul,
    fullHomPostcomp_homotopy_inverse k n v b hunit, hscalar]
  change x.2 + (n+1).negOnePow • (c • x.1) = _
  rw [TriangleGradedSequence.integerUnit_smul k, add_comm]

omit [CharP k 2] [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F]
  [SMulCommClass k Rᵐᵒᵖ F] in
theorem tensorComparison_bijective_of_coordinates (n : ℤ)
    (E : CohomologyClass P (tensorCochain (k := k) (F := F) P) n ≃ₗ[k]
      (CohomologyClass P P n × CohomologyClass P P n))
    (a b : k) (hab : a ≠ b)
    (hE : ∀ x, E (tensorComparison v n x) = twoTwistLinear a b x) :
    Function.Bijective (tensorComparison v n) := by
  constructor
  · intro x y h
    apply twoTwistLinear_injective a b hab
    rw [← hE, ← hE, h]
  · intro y
    obtain ⟨x, hx⟩ := twoTwistLinear_surjective a b hab (E y)
    exact ⟨x, E.injective ((hE x).trans hx)⟩

end ArExplicit.TriangularInduction

end

end OAI
