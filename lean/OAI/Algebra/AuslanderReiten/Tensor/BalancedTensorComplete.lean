import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorCokernel
import OAI.Algebra.AuslanderReiten.Complete.CompleteShiftDual

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor
open CategoryTheory
universe u
variable {k R S F : Type u} [Field k] [Ring R] [Ring S] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module S F]
variable [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
variable [Module.Finite S F] [Module.Projective S F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

theorem complex_exactProjective (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ExactProjectiveCochain P) :
    ExactProjectiveCochain
      (((functor (k := k) (R := R) (S := S) (F := F)).mapHomologicalComplex _).obj P) where
  finite n := by
    let := hP.finite n
    exact finite
  projective n := by
    let := hP.finite n
    let := hP.projective n
    exact projective
  exactAt n := by
    rw [HomologicalComplex.exactAt_iff' _ (n-1) n (n+1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    have he := hP.exactAt n
    rw [HomologicalComplex.exactAt_iff' _ (n-1) n (n+1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker] at he
    exact (LinearMap.exact_iff.mp
      (mapRight_exact (k := k) (F := F) (S := S) _ _
        (LinearMap.exact_iff.mpr he.symm))).symm

theorem complex_totallyAcyclic [Module.Injective S S]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : ExactProjectiveCochain P) :
    TotallyAcyclicCochain
      (((functor (k := k) (R := R) (S := S) (F := F)).mapHomologicalComplex _).obj P) :=
  TotallyAcyclicCochain.of_chain
    (complex_exactProjective (k := k) (F := F) (S := S) P hP).to_chain.totallyAcyclic

end ArExplicit.BalancedTensor

end

end OAI
