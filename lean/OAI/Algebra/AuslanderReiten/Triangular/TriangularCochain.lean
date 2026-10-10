import OAI.Algebra.AuslanderReiten.Triangular.TriangularCategory
import OAI.Algebra.AuslanderReiten.Complete.CompleteShiftDual

namespace OAI

noncomputable section

namespace ArExplicit.TriangularInduction

open CategoryTheory

universe u

variable {k R F : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

abbrev eCochain (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((eFunctor k R F).mapHomologicalComplex _).obj P

abbrev jCochain (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((jFunctor k R F).mapHomologicalComplex _).obj P

variable [Module.Finite k R] [Module.Finite k F]

theorem eCochain_totallyAcyclic [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : TotallyAcyclicCochain P) :
    TotallyAcyclicCochain (eCochain (k := k) (F := F) P) where
  finite n := by
    let := hP.finite n
    let : Module.Finite k (P.X n) := Module.Finite.trans R (P.X n)
    exact Module.Finite.of_restrictScalars_finite k (Triangular R F) (TriangularE k R F (P.X n))
  projective n := by
    let := hP.finite n
    let := hP.projective n
    exact eProjective
  exactAt n := by
    rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    have h := hP.exactAt n
    rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker] at h
    exact (LinearMap.exact_iff.mp (eMap_exact (k := k) (F := F) _ _
      (LinearMap.exact_iff.mpr h.symm))).symm
  dualExact n := eHomExact _ _ (hP.dualExact n)

omit [Module.Finite k F] in
theorem jCochain_totallyAcyclic [Module.Finite R F] [Module.Projective R F]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : TotallyAcyclicCochain P) :
    TotallyAcyclicCochain (jCochain (k := k) (F := F) P) where
  finite n := by
    let := hP.finite n
    let : Module.Finite k (P.X n) := Module.Finite.trans R (P.X n)
    exact Module.Finite.of_restrictScalars_finite k (Triangular R F) (TriangularJ k R F (P.X n))
  projective n := by
    let := hP.finite n
    let := hP.projective n
    exact jProjective
  exactAt n := by
    rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    have h := hP.exactAt n
    rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker] at h
    exact (LinearMap.exact_iff.mp (jMap_exact (k := k) (F := F) _ _
      (LinearMap.exact_iff.mpr h.symm))).symm
  dualExact n := jHomExact _ _ (hP.dualExact n)

end ArExplicit.TriangularInduction

end

end OAI
