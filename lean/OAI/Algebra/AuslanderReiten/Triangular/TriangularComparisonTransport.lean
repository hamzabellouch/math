import OAI.Algebra.AuslanderReiten.Triangular.TriangularComparison

namespace OAI

noncomputable section
namespace ArExplicit.TriangularInduction
open CategoryTheory CochainComplex.HomComplex
universe u
variable {k R F : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {P : CochainComplex (ModuleCat.{u} R) ℤ}
variable (v : P ⟶ tensorCochain (k := k) (F := F) P) (n : ℤ)

def comparisonSourceEquiv :
    (CohomologyClass P P n × CohomologyClass P P n) ≃+
      (CohomologyClass (eCochain (k := k) (F := F) P)
        (eCochain (k := k) (F := F) P) n ×
       CohomologyClass (jCochain (k := k) (F := F) P)
        (jCochain (k := k) (F := F) P) n) :=
  AddEquiv.prodCongr (fullHomCohomologyEquiv (eFunctor k R F) P P n)
    (fullHomCohomologyEquiv (jFunctor k R F) P P n)

@[simp] theorem comparisonSourceEquiv_apply (a b : CohomologyClass P P n) :
    comparisonSourceEquiv (F := F) (P := P) n (a,b) =
      (fullHomCohomologyEquiv (eFunctor k R F) P P n a,
        fullHomCohomologyEquiv (jFunctor k R F) P P n b) := rfl

theorem coneComparison_injective_of_tensor
    (h : Function.Injective (tensorComparison v n)) :
    Function.Injective (coneComparison (crossChainMap v) n) := by
  intro x y hxy
  obtain ⟨a,rfl⟩ := (comparisonSourceEquiv (F := F) (P := P) n).surjective x
  obtain ⟨b,rfl⟩ := (comparisonSourceEquiv (F := F) (P := P) n).surjective y
  apply congrArg
  apply h
  apply (crossCohomologyEquiv P P n).injective
  rw [cross_tensorComparison, cross_tensorComparison]
  exact hxy

theorem coneComparison_surjective_of_tensor
    (h : Function.Surjective (tensorComparison v n)) :
    Function.Surjective (coneComparison (crossChainMap v) n) := by
  intro y
  obtain ⟨x,hx⟩ := h ((crossCohomologyEquiv P P n).symm y)
  refine ⟨comparisonSourceEquiv (F := F) (P := P) n x, ?_⟩
  rcases x with ⟨a,b⟩
  rw [comparisonSourceEquiv_apply, ← cross_tensorComparison, hx, AddEquiv.apply_symm_apply]

theorem coneComparison_nonzero_kernel_of_tensor
    (h : ∃ x : CohomologyClass P P n × CohomologyClass P P n,
      x ≠ 0 ∧ tensorComparison v n x = 0) :
    ∃ x : CohomologyClass (eCochain (k := k) (F := F) P)
        (eCochain (k := k) (F := F) P) n ×
      CohomologyClass (jCochain (k := k) (F := F) P)
        (jCochain (k := k) (F := F) P) n,
      x ≠ 0 ∧ coneComparison (crossChainMap v) n x = 0 := by
  obtain ⟨x,hx,h0⟩ := h
  refine ⟨comparisonSourceEquiv (F := F) (P := P) n x, ?_, ?_⟩
  · exact fun he => hx ((comparisonSourceEquiv (F := F) (P := P) n).map_eq_zero_iff.mp he)
  · rcases x with ⟨a,b⟩
    rw [comparisonSourceEquiv_apply, ← cross_tensorComparison, h0, map_zero]

end ArExplicit.TriangularInduction

end

end OAI
