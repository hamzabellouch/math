import OAI.Algebra.AuslanderReiten.Ext.ExtKunneth
import OAI.Algebra.AuslanderReiten.Ext.TTensorPolynomial
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorScalarExt
import OAI.Algebra.AuslanderReiten.Algebras.TensorSimple
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorExt

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T" => ArExplicit.T k q
local notation "S" => ModuleCat.of T (Simple q)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

abbrev ASelfExt (n : ℕ) := Ext (ArExplicit.A.Simple q) (ArExplicit.A.Simple q) n

abbrev aCanonicalKunnethEquiv (n : ℕ) :=
  ModuleBar.nativeTensorKunneth k T T (Simple q) (Simple q) n

abbrev aExtKunnethEquiv (n : ℕ) :=
  ModuleBar.tensorKunneth k T T (Simple q) (Simple q) n

variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : NoPositivePowerOne q)

abbrev aExtCoefficientEquiv (n : ℕ) :=
  (aExtKunnethEquiv q (3*n)).trans (tTensorCoefficientEquiv q hq hq1 h n)

include hq hq1 h in

theorem aSelfExt_zero_of_not_dvd (n : ℕ) (hn : ¬ 3 ∣ n) (x : ASelfExt q n) : x=0 := by
  exact (aExtKunnethEquiv q n).map_eq_zero_iff.mp
    (tTensorCoefficient_zero_of_not_dvd q hq hq1 h n hn (aExtKunnethEquiv q n x))

def aMonomial (n : ℕ) (i : Fin (n+1)) : ASelfExt q (3*n) :=
  (aExtCoefficientEquiv q hq hq1 h n).symm (Pi.single i 1)

end ArExplicit.Resolution

end

end OAI
