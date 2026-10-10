import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedCollisionOptionBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected
open Construction

theorem cmean_option_real_scale {α β Ω : Type*} [Fintype Ω]
    (μ : FinitePrior Ω) (z : Option α) (ρ : α → β)
    (f : α → Ω → ℂ) (K : β → ℂ) (D : α → ℝ) (G : β → Ω → ℂ)
    (hf : ∀ r u, f r u = K (ρ r) * ((D r : ℂ) * G (ρ r) u)) :
    μ.cmean (fun u => z.elim 0 (fun r => f r u)) =
      (z.map ρ).elim 0 (fun r => K r * μ.cmean (fun u => ((z.elim 0 D : ℝ) : ℂ) * G r u)) := by
  cases z with
  | none =>
      simp only [Option.elim_none, Option.map_none, FinitePrior.cmean,
        Finset.sum_const_zero, mul_zero]
  | some r =>
      simp only [Option.elim_some, Option.map_some, hf]
      exact μ.cmean_mul_left _ _

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
