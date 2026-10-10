import OAI.Algebra.AuslanderReiten.Resolutions.ConcreteKoszulCoordinates
import OAI.Algebra.AuslanderReiten.Resolutions.SimpleCoverCubicConjugate
import OAI.Algebra.AuslanderReiten.Complete.ConcreteTateModel
import OAI.Algebra.AuslanderReiten.Resolutions.BinaryKoszulScalar

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (A k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : Resolution.NoPositivePowerOne q)
local notation "H₀" => fun d => CohomologyClass (A.simpleComplete q) (A.simpleComplete q) d
include hq hq1 h

def coverTateModel : TateKoszul.Model (firstCoverOperator q) (secondCoverOperator q) := by
  unfold firstCoverOperator secondCoverOperator
  rw [firstCoverClass_eq q hq1, secondCoverClass_eq q hq1]
  exact A.tateModel q hq hq1 h

theorem twoConeHom_subsingleton (a : ℤ) (h0 : a ≠ 0) (h3 : a ≠ 3) :
    Subsingleton (twoConeHom q a) :=
  (concreteKoszulCoordinates q).subsingleton_of_ne (coverTateModel q hq hq1 h) a h0 h3

def twoConeTopEquiv : twoConeHom q 3 ≃ₗ[k] H₀ (-1) :=
  (concreteKoszulCoordinates q).topCoordinateEquiv (coverTateModel q hq hq1 h)

theorem twoConeTopEquiv_apply (w : twoConeHom q 3) :
    twoConeTopEquiv q hq hq1 h w =
      twoConeTopCoordinate q 3 ((concreteTwoConeFiltration q).projection 3 w) := rfl

def twoConeZeroEquiv : twoConeHom q 0 ≃ₗ[k] H₀ 0 :=
  (concreteKoszulCoordinates q).bottomCoordinateEquiv (coverTateModel q hq hq1 h)

def twoConeZeroScalarEquiv : twoConeHom q 0 ≃ₗ[k] k :=
  (twoConeZeroEquiv q hq hq1 h).trans (A.fullHomZeroScalarEquiv q hq1)

def twoConeTopScalarEquiv : twoConeHom q 3 ≃ₗ[k] k :=
  ((twoConeTopEquiv q hq hq1 h).trans ((coverTateModel q hq hq1 h).negative 0)).trans
    (BinaryKoszul.zeroDualPieceScalarEquiv k)

end ArExplicit.T

end

end OAI
