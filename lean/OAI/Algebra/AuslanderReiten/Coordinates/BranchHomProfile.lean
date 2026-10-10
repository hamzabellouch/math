import OAI.Algebra.AuslanderReiten.Coordinates.BranchHomCoordinates
import OAI.Algebra.AuslanderReiten.Cones.ConcreteTwoConeProfile

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (A k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : Resolution.NoPositivePowerOne q)
include hq hq1 h

theorem branchHom_subsingleton (a : ℤ) (h0 : a ≠ 0) (h3 : a ≠ -3) :
    Subsingleton (BranchHom q a) := by
  let := twoConeHom_subsingleton q hq hq1 h (a+3) (by omega) (by omega)
  exact (branchHomEquiv q a).injective.subsingleton

def branchZeroScalarEquiv : BranchHom q 0 ≃ₗ[k] k :=
  (branchHomEquiv q 0).trans (twoConeTopScalarEquiv q hq hq1 h)

def branchPlainScalarEquiv :
    (evaluatedSimpleObject q ⟶ branchTargetObject q) ≃ₗ[k] k :=
  (branchPlainHomEquiv q).trans (twoConeTopScalarEquiv q hq hq1 h)

end ArExplicit.T

end

end OAI
