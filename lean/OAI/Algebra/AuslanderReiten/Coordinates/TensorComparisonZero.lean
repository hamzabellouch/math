import OAI.Algebra.AuslanderReiten.Triangular.TriangularComparison
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorLinear
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomMapLinear

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

theorem tensorComparison_scalarIdentity (a b : k) :
    tensorComparison v 0
      (a • CohomologyClass.mk (Cocycle.ofHom (𝟙 P)),
       b • CohomologyClass.mk (Cocycle.ofHom (𝟙 P))) =
      (b-a) • CohomologyClass.mk (Cocycle.ofHom v) := by
  change fullHomPostcomp v 0 (b • CohomologyClass.mk (Cocycle.ofHom (𝟙 P))) +
    (0+1 : ℤ).negOnePow • fullHomPrecomp v 0
      (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)) P P 0
        (a • CohomologyClass.mk (Cocycle.ofHom (𝟙 P)))) = _
  rw [fullHomPostcomp_smul, fullHomPostcomp_identity, mapFullHom_smul,
    mapFullHom_identity, fullHomPrecomp_smul, fullHomPrecomp_identity]
  rw [show (0+1 : ℤ).negOnePow = (-1 : ℤˣ) by decide, Units.smul_def]
  change b • CohomologyClass.mk (Cocycle.ofHom v) +
    (-1 : ℤ) • (a • CohomologyClass.mk (Cocycle.ofHom v)) = _
  rw [neg_one_zsmul, sub_smul, sub_eq_add_neg]

theorem tensorComparison_zero_surjective
    (hv : ∀ z : CohomologyClass P (tensorCochain (k := k) (F := F) P) 0,
      ∃ a : k, a • CohomologyClass.mk (Cocycle.ofHom v) = z) :
    Function.Surjective (tensorComparison v 0) := by
  intro z
  obtain ⟨a,rfl⟩ := hv z
  refine ⟨((0 : k) • CohomologyClass.mk (Cocycle.ofHom (𝟙 P)),
    a • CohomologyClass.mk (Cocycle.ofHom (𝟙 P))), ?_⟩
  rw [tensorComparison_scalarIdentity, sub_zero]

theorem tensorComparison_zero_nonzero_kernel
    (hid : CohomologyClass.mk (Cocycle.ofHom (𝟙 P)) ≠ 0) :
    ∃ w : CohomologyClass P P 0 × CohomologyClass P P 0,
      w ≠ 0 ∧ tensorComparison v 0 w = 0 := by
  refine ⟨(CohomologyClass.mk (Cocycle.ofHom (𝟙 P)),
    CohomologyClass.mk (Cocycle.ofHom (𝟙 P))), ?_, ?_⟩
  · intro hw
    exact hid (congrArg Prod.fst hw)
  · simpa only [one_smul, sub_self, zero_smul] using
      tensorComparison_scalarIdentity v (1 : k) 1

end ArExplicit.TriangularInduction

end

end OAI
