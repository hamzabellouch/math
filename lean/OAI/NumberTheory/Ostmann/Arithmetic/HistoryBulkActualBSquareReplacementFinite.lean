import OAI.NumberTheory.Ostmann.Construction.ActualAmplitude
import OAI.NumberTheory.Ostmann.Construction.OffDiagonalExpectations

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement
open Construction

theorem norm_nested_root_sum_sub_le {α β ι κ τ : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [Fintype κ] [Fintype τ]
    (μ : FinitePrior α) (ν : FinitePrior β) (F G : α → β → ι×(κ×τ) → ℂ) :
    ‖μ.cmean (fun a => ν.cmean (fun b => ∑i,F a b i))-
      μ.cmean (fun a => ν.cmean (fun b => ∑i,G a b i))‖ ≤
    ∑i,∑j,∑k,‖(μ.pair ν).cmean (fun a => F a.1 a.2 (i,(j,k)))-
      (μ.pair ν).cmean (fun a => G a.1 a.2 (i,(j,k)))‖ := by
  simp_rw [FinitePrior.cmean_sum]
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑i,‖μ.cmean (fun a=>ν.cmean (fun b=>F a b i))-
        μ.cmean (fun a=>ν.cmean (fun b=>G a b i))‖ := norm_sum_le _ _
    _ = _ := by simp only [Fintype.sum_prod_type,FinitePrior.pair_cmean]

end Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement

end

end OAI
