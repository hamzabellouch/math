import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernelStageSum

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction

theorem option_cmean_eq_of_point {α δ : Type*} [Fintype α]
    (μ : FinitePrior α) (opt : Option δ)
    (A : δ → α → ℂ) (K : δ → ℂ) (F : δ → α → ℂ)
    (h : ∀r u,A r u=K r*F r u) :
    μ.cmean (fun u=>opt.elim 0 (fun r=>A r u)) =
      opt.elim 0 (fun r=>K r*μ.cmean (F r)) := by
  have he : (fun u=>opt.elim 0 (fun r=>A r u)) =
      (fun u=>opt.elim 0 (fun r=>K r*F r u)) := by
    funext u
    cases opt with
    | none => rfl
    | some r => exact h r u
  exact (congrArg μ.cmean he).trans (kernelStage_option_cmean_mul μ opt K F)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
