import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteBranchBeta
import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteBetaValue
import OAI.Algebra.AuslanderReiten.Homology.DimensionOneDetector

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (hq1 : 1+q ≠ 0)

theorem branchBetaDetector_eq_beta (H : kˣ) :
    branchBetaDetector q hq1 (branchHom q H) = A.betaHom q := by
  exact (branchBetaDetector_value q hq1 H).trans
    (congrArg (fun f : (A.simpleFiniteModule q).carrier →ₗ[A k q]
        (A.betaFiniteModule q).carrier =>
      (HomotopyCategory.quotient _ _).map
        (FiniteLeftModule.resolutionMap (AFrobeniusTrace k q)
          (M := A.simpleFiniteModule q) (N := A.betaFiniteModule q) f))
      (betaTransfer_normalizedBranchTop q hq1 H))

variable (e : (evaluatedSimpleObject q ⟶ branchTargetObject q) ≃ₗ[k] k)
include hq1 e

theorem branchHom_common_of_scalarCoordinate (H₁ H₂ : kˣ) :
    branchHom q H₁ = branchHom q H₂ :=
  (scalarDetector_common e (branchBetaDetector q hq1)
    (branchHom q H₁) (branchHom q H₂) (A.betaHom q) (A.betaHom_ne_zero q hq1)
    (branchBetaDetector_eq_beta q hq1 H₁) (branchBetaDetector_eq_beta q hq1 H₂)).1

theorem branchHom_ne_zero_of_scalarCoordinate (H : kˣ) :
    branchHom q H ≠ 0 :=
  (scalarDetector_common e (branchBetaDetector q hq1)
    (branchHom q H) (branchHom q H) (A.betaHom q) (A.betaHom_ne_zero q hq1)
    (branchBetaDetector_eq_beta q hq1 H) (branchBetaDetector_eq_beta q hq1 H)).2

end ArExplicit.T

end

end OAI
