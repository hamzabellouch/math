import OAI.Algebra.AuslanderReiten.Coordinates.ConcreteCubicClasses
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarPositiveModel
import OAI.Algebra.AuslanderReiten.Homology.AEndHomScalar
import OAI.Algebra.AuslanderReiten.Ext.TTensorGeneration

namespace OAI

noncomputable section
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.A
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.A k q))]
open CompleteComparison

private def rawPositiveModel (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (h : Resolution.NoPositivePowerOne q) :=
  ModuleBar.tensorPositiveModel k (ArExplicit.T k q) (ArExplicit.T k q)
    (Resolution.Simple q) (Resolution.Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (Resolution.tExplicitP q) (Resolution.aFactorExtClass q)
    (Resolution.tExplicitP q) (Resolution.aFactorExtClass q)
    (Resolution.tTensor_generation q hq hq1 h) (Resolution.aEndHom_scalar q hq1)
    (simpleComplete q) (nonnegativeExtChart q hq1)
    (Resolution.tTensorCoefficientEquiv q hq hq1 h)
    (Resolution.tTensorCoefficient_zero_of_not_dvd q hq hq1 h)
    (Resolution.tTensorCoefficient_first q hq hq1 h)
    (Resolution.tTensorCoefficient_second q hq hq1 h)

def positiveTateModel (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : Resolution.NoPositivePowerOne q) : FullTate.PositiveModel (k := k) (simpleComplete q)
    (firstFullClass q hq1) (secondFullClass q hq1) :=
  rawPositiveModel q hq hq1 h

def tateModel (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : Resolution.NoPositivePowerOne q) : TateKoszul.Model
    (fun a => fullHomRightMultiply (k := k) (K := simpleComplete q) (n := a) (firstFullClass q hq1))
    (fun a => fullHomRightMultiply (k := k) (K := simpleComplete q) (n := a) (secondFullClass q hq1)) :=
  FullTate.model (AFrobeniusTrace k q) (A_trace_symmetric k q)
    ((simpleFiniteModule q).completeCochain_totallyAcyclic (AFrobeniusTrace k q)).to_chain
    (positiveTateModel q hq hq1 h)

end ArExplicit.A

end

end OAI
