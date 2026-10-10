import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteBetaTransfer
import OAI.Algebra.AuslanderReiten.Coordinates.NormalizedBranchValue
import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteFreeValue

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (hq1 : 1+q ≠ 0)
local notation "D" => bimoduleTwoConeData q
local notation "hf" => bimodule_term_finite_k q

theorem betaTransfer_normalizedBranchTop_of_freeEvaluation
    (hfree : ∀ (z : (D).term 0) (s t : Resolution.Simple q),
      freeCoordinateRaw q hq1 (BalancedTensor.tmul
        (⟨z⟩ : EnvelopingBimodule k (A k q) (TwoCone.termModule D hf 0).carrier)
        (s ⊗ₜ[k] t)) = endpointEvaluation q s t z)
    (H : kˣ) :
    (betaTransfer q hq1).comp (normalizedBranchTop q H) = A.beta q := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact ((map_add ((betaTransfer q hq1).comp (normalizedBranchTop q H)) x y).trans
      (congrArg₂ (· + ·) hx hy)).trans (map_add (A.beta q) x y).symm
  | tmul s t =>
    apply Subtype.ext
    change betaTransferRaw q hq1 (normalizedBranchTop q H (s ⊗ₜ[k] t)) =
      A.socleMap q (s ⊗ₜ[k] t)
    erw [normalizedBranchTop_apply]
    change freeCoordinateRaw q hq1 (BalancedTensor.tmul
      (⟨TwoCone.baseStepInclusion D (bimodule_exact q) 0
        (normalizedSourceTop q H (sourceUnit q H))⟩ :
        EnvelopingBimodule k (A k q) (TwoCone.termModule D hf 0).carrier)
      (s ⊗ₜ[k] t)) = _
    rw [hfree]
    exact normalizedSourceTop_evaluated q H hq1 s t

theorem betaTransfer_normalizedBranchTop (H : kˣ) :
    (betaTransfer q hq1).comp (normalizedBranchTop q H) = A.beta q :=
  betaTransfer_normalizedBranchTop_of_freeEvaluation q hq1
    (freeCoordinateRaw_endpoint q hq1) H

end ArExplicit.T

end

end OAI
