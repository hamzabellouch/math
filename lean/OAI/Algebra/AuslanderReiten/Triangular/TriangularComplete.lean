import OAI.Algebra.AuslanderReiten.Triangular.TriangularExact
import OAI.Algebra.AuslanderReiten.Triangular.TriangularDualExact
import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionComplete
import OAI.Algebra.AuslanderReiten.Complete.CompleteComparison

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

private instance moduleCatBaseComm (M : ModuleCat.{u} R) : SMulCommClass k R M where
  smul_comm c r m := by
    change (algebraMap k R c) • (r • m) = r • ((algebraMap k R c) • m)
    rw [← mul_smul, Algebra.commutes c r, mul_smul]

def eComplex (P : ChainComplex (ModuleCat.{u} R) ℤ) :
    ChainComplex (ModuleCat.{u} (Triangular R F)) ℤ where
  X n := ModuleCat.of (Triangular R F) (TriangularE k R F (P.X n))
  d i j := ModuleCat.ofHom (eMap (P.d i j).hom)
  shape i j hij := by
    rw [P.shape i j hij]
    apply ModuleCat.hom_ext
    exact eMap_zero
  d_comp_d' i j l _ _ := by
    apply ModuleCat.hom_ext
    change (eMap (P.d j l).hom).comp (eMap (P.d i j).hom) = 0
    rw [← eMap_comp, show (P.d j l).hom.comp (P.d i j).hom = 0 from
      congrArg ModuleCat.Hom.hom (P.d_comp_d i j l), eMap_zero]

def jComplex (P : ChainComplex (ModuleCat.{u} R) ℤ) :
    ChainComplex (ModuleCat.{u} (Triangular R F)) ℤ where
  X n := ModuleCat.of (Triangular R F) (TriangularJ k R F (P.X n))
  d i j := ModuleCat.ofHom (jMap (P.d i j).hom)
  shape i j hij := by
    rw [P.shape i j hij]
    apply ModuleCat.hom_ext
    exact jMap_zero
  d_comp_d' i j l _ _ := by
    apply ModuleCat.hom_ext
    change (jMap (P.d j l).hom).comp (jMap (P.d i j).hom) = 0
    rw [← jMap_comp, show (P.d j l).hom.comp (P.d i j).hom = 0 from
      congrArg ModuleCat.Hom.hom (P.d_comp_d i j l), jMap_zero]

variable [Module.Finite k R] [Module.Finite k F]

theorem eComplex_totallyAcyclic [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
    (P : ChainComplex (ModuleCat.{u} R) ℤ) (hP : TotallyAcyclicComplex P) :
    TotallyAcyclicComplex (eComplex (k := k) (F := F) P) where
  finite n := by
    let := hP.finite n
    let : Module.Finite k (P.X n) := Module.Finite.trans R (P.X n)
    exact Module.Finite.of_restrictScalars_finite k (Triangular R F) (TriangularE k R F (P.X n))
  projective n := by
    let := hP.finite n
    let := hP.projective n
    exact eProjective
  exactAt n :=
    (LinearMap.exact_iff.mp (eMap_exact (k := k) (F := F) _ _
      (LinearMap.exact_iff.mpr (hP.exactAt n).symm))).symm
  dualExact n := eHomExact _ _ (hP.dualExact n)

omit [Module.Finite k F] in
theorem jComplex_totallyAcyclic [Module.Finite R F] [Module.Projective R F]
    (P : ChainComplex (ModuleCat.{u} R) ℤ) (hP : TotallyAcyclicComplex P) :
    TotallyAcyclicComplex (jComplex (k := k) (F := F) P) where
  finite n := by
    let := hP.finite n
    let : Module.Finite k (P.X n) := Module.Finite.trans R (P.X n)
    exact Module.Finite.of_restrictScalars_finite k (Triangular R F) (TriangularJ k R F (P.X n))
  projective n := by
    let := hP.finite n
    let := hP.projective n
    exact jProjective
  exactAt n :=
    (LinearMap.exact_iff.mp (jMap_exact (k := k) (F := F) _ _
      (LinearMap.exact_iff.mpr (hP.exactAt n).symm))).symm
  dualExact n := jHomExact _ _ (hP.dualExact n)

end ArExplicit.TriangularInduction

end

end OAI
