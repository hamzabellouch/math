import OAI.NumberTheory.Ostmann.Construction.OffDiagonalExpectations

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected
open Construction

theorem cmean_cmean_sum {α β κ : Type*} [Fintype α] [Fintype β] [Fintype κ]
    (μ : FinitePrior α) (ν : FinitePrior β) (F : α → β → κ → ℂ) :
    μ.cmean (fun a => ν.cmean (fun b => ∑ i, F a b i)) =
      ∑ i, μ.cmean (fun a => ν.cmean (fun b => F a b i)) :=
  (congrArg μ.cmean (funext fun a =>
    ν.cmean_sum Finset.univ (fun i b => F a b i))).trans
      (μ.cmean_sum Finset.univ (fun i a => ν.cmean (fun b => F a b i)))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
