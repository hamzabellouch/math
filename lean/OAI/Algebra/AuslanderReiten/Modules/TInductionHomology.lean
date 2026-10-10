import OAI.Algebra.AuslanderReiten.Duality.IdealDualHomology
import OAI.Algebra.AuslanderReiten.Resolutions.TrivialInductionDual
import OAI.Algebra.AuslanderReiten.Homology.ConcentratedNatDerived
import OAI.Algebra.AuslanderReiten.Algebras.TSimple

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "C" => BaseAlgebra k q
local notation "T" => ArExplicit.T k q

def inflatedSimpleIso :
    (TrivialInduction.inflate (k := k)).obj (ModuleCat.of C (Simple q)) ≅
      ModuleCat.of T (Simple q) := Iso.refl _

def dualIdealComparison :
    TrivialInduction.dualComplex (k := k) (complex q) ≅
      ((TrivialInduction.inflate (k := k)).mapHomologicalComplex _).obj (idealDualComplex q) :=
  TrivialInduction.dualComplexIso (complex q) ≪≫
    ((TrivialInduction.inflate (k := k)).mapHomologicalComplex _).mapIso (tensorIdealComparison q)

theorem tDual_exact (hq : q ≠ 0) (h : NoPositivePowerOne q) (n : ℕ) (hn : n ≠ 2) :
    (TrivialInduction.dualComplex (k := k) (complex q)).ExactAt n := by
  apply (exactAt_iff_of_quasiIsoAt (dualIdealComparison q).hom n).mpr
  exact ModuleRestriction.map_exact _ _ (idealDual_exactAt q hq h n hn)

def tDual_homology_iso (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    (TrivialInduction.dualComplex (k := k) (complex q)).homology 2 ≅ ModuleCat.of T (Simple q) :=
  HomologicalComplex.homologyMapIso (dualIdealComparison q) 2 ≪≫
    ((idealDualComplex q).sc 2).mapHomologyIso (TrivialInduction.inflate (k := k)) ≪≫
    (TrivialInduction.inflate (k := k)).mapIso (idealDual_homology_two_iso q hq hq1) ≪≫
    inflatedSimpleIso q

def tDualDerivedIso [HasDerivedCategory (ModuleCat T)]
    (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q) :
    DerivedCategory.Q.obj
      ((TrivialInduction.dualComplex (k := k) (complex q)).extend ComplexShape.embeddingDownNat) ≅
      ((DerivedCategory.singleFunctor (ModuleCat T) 0).obj (ModuleCat.of T (Simple q)))⟦(2 : ℤ)⟧ :=
  concentratedNatDerivedIso _ 2 _ (tDual_exact q hq h) (tDual_homology_iso q hq hq1)

theorem tQuotient_exact (h : NoPositivePowerOne q) (n : ℕ) (hn : n ≠ 0) :
    (TrivialInduction.quotientComplex (k := k) (complex q)).ExactAt n := by
  apply (exactAt_iff_of_quasiIsoAt
    (TrivialInduction.quotientComplexIso (complex q)).hom n).mpr
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact ModuleRestriction.map_exact _ _ (complex_exactAt_succ q h m)

def cResolution_homology_zero (h : NoPositivePowerOne q) :
    (complex q).homology 0 ≅ ModuleCat.of C (Simple q) := by
  letI := toSimple_quasiIso q h
  exact isoOfQuasiIsoAt (toSimple q) 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso _ _ _

def tQuotient_homology_iso (h : NoPositivePowerOne q) :
    (TrivialInduction.quotientComplex (k := k) (complex q)).homology 0 ≅ ModuleCat.of T (Simple q) :=
  HomologicalComplex.homologyMapIso (TrivialInduction.quotientComplexIso (complex q)) 0 ≪≫
    ((complex q).sc 0).mapHomologyIso (TrivialInduction.inflate (k := k)) ≪≫
    (TrivialInduction.inflate (k := k)).mapIso (cResolution_homology_zero q h) ≪≫
    inflatedSimpleIso q

def tQuotientDerivedIso [HasDerivedCategory (ModuleCat T)]
    (h : NoPositivePowerOne q) :
    DerivedCategory.Q.obj
      ((TrivialInduction.quotientComplex (k := k) (complex q)).extend ComplexShape.embeddingDownNat) ≅
      (DerivedCategory.singleFunctor (ModuleCat T) 0).obj (ModuleCat.of T (Simple q)) :=
  concentratedNatDerivedIso _ 0 _ (tQuotient_exact q h) (tQuotient_homology_iso q h) ≪≫
    (shiftFunctorZero _ ℤ).app _

end ArExplicit.Resolution

end

end OAI
