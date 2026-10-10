import OAI.Algebra.AuslanderReiten.Homology.FullPositiveModel
import OAI.Algebra.AuslanderReiten.HomComplex.TensorFullHomPositive
import OAI.Algebra.AuslanderReiten.Ext.AExtActions

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

def firstFullClass (hq1 : 1+q ≠ 0) : CohomologyClass (simpleComplete q) (simpleComplete q) 3 :=
  (fullNonnegativeExtEquiv q hq1 3).symm (Resolution.aFirst q)

def secondFullClass (hq1 : 1+q ≠ 0) : CohomologyClass (simpleComplete q) (simpleComplete q) 3 :=
  (fullNonnegativeExtEquiv q hq1 3).symm (Resolution.aSecond q)

def nonnegativeExtChart (hq1 : 1+q ≠ 0) : FullPositive.NonnegativeChart (k := k) (simpleComplete q) (Simple q) where
  equiv := fullNonnegativeExtEquiv q hq1
  product := fullNonnegativeExtEquiv_product q hq1

end ArExplicit.A

end

end OAI
