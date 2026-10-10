import OAI.NumberTheory.Ostmann.Construction.JoinedRemaining
import OAI.NumberTheory.Ostmann.Construction.OffDiagonalExpectations

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected
open Construction

theorem weighted_cmean_factor {α β : Type*} [Fintype α] [Fintype β]
    (w : α→ℝ) (μ : FinitePrior β) (J : α→ℂ) (F G : α→β→ℂ)
    (h : ∀a,w a≠0→∀b,μ.mass b≠0→F a b=J a*G a b) :
    (∑a,(w a:ℂ)*μ.cmean (F a)) =
      ∑a,(w a:ℂ)*J a*μ.cmean (G a) := by
  classical
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : w a=0
  · simp only [ha,Complex.ofReal_zero,zero_mul]
  · rw [mul_assoc]
    apply congrArg ((w a:ℂ)*·)
    rw [←FinitePrior.cmean_mul_left]
    apply FinitePrior.cmean_congr_support
    exact h a ha

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
