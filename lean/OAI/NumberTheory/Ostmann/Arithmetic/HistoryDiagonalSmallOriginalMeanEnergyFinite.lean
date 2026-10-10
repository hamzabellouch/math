import OAI.NumberTheory.Ostmann.Construction.AssignmentReinsert
import OAI.NumberTheory.Ostmann.Construction.OffDiagonalExpectations

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMean
open Construction

theorem restoringAssignment_cmean (sources : SourceFamily) (j : ℕ) (T : List SourceSlot)
    (F : SourceAssignment sources (Template.extracted j T) ×
      SourceAssignment sources (Template.remainder j T) → ℂ) :
    (assignmentPrior sources T).cmean (fun x => F (restoringAssignmentEquiv sources j T x)) =
      (assignmentPrior sources (Template.extracted j T)).cmean (fun u =>
        (assignmentPrior sources (Template.remainder j T)).cmean (fun x => F (u,x))) := by
  have he := (restoringSplit sources j T).val.csum_comp F
  simpa only [FinitePrior.cmean, Fintype.sum_prod_type, Complex.ofReal_mul,
    assignmentWeight_eq_mass, restoringAssignmentEquiv, Finset.mul_sum, mul_assoc] using he

theorem weighted_pair_frequency_cmean {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (μ : FinitePrior α) (ν : FinitePrior β) (S : Finset δ)
    (w : δ → ℂ) (F : δ → α → β → γ → ℂ) :
    (∑ p ∈ S, w p * (μ.pair ν).cmean (fun z => ∑ v, F p z.1 z.2 v)) =
      ν.cmean (fun x => ∑ v, ∑ p ∈ S, w p * μ.cmean (fun q => F p q x v)) := by
  simp_rw [FinitePrior.pair_cmean, FinitePrior.cmean_comm μ ν]
  simp_rw [← FinitePrior.cmean_mul_left ν]
  rw [← FinitePrior.cmean_sum]
  apply congrArg (FinitePrior.cmean ν)
  funext x
  simp_rw [FinitePrior.cmean_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem weighted_pair_frequency_cmean_factor {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (μ : FinitePrior α) (ν : FinitePrior β) (S : Finset δ)
    (w : δ → ℂ) (c : ℂ) (A B : δ → α → β → γ → ℂ) :
    (∑ p ∈ S, w p * (μ.pair ν).cmean
      (fun z => ∑ v, A p z.1 z.2 v * (c * B p z.1 z.2 v))) =
      c * ν.cmean (fun x => ∑ v, ∑ p ∈ S,
        w p * μ.cmean (fun q => A p q x v * B p q x v)) := by
  have hc : ∀ a b : ℂ, a * (c * b) = c * (a * b) := by
    intro a b
    ring
  simp_rw [hc, ← Finset.mul_sum, FinitePrior.cmean_mul_left,
    mul_left_comm (w _) c, ← Finset.mul_sum]
  congr 1
  exact weighted_pair_frequency_cmean μ ν S w (fun p q x v => A p q x v * B p q x v)

end Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMean

end

end OAI
