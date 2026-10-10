import OAI.NumberTheory.Ostmann.Arithmetic.GiantCollisionError
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageBudget
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedRootErrorBudget

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage
open Construction Conclusion Filter HistoryGiantOriginalMeanFactorization

theorem selected_nested_choices_error_eventually
    (d : Decomposition) (Bs BD Bz H : ℝ) (hH : 0 ≤ H) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20 : ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter : ℝ) →
      (C.giantCenter : ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin : ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin : ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ l ≤ k, ∀ (α β : Type*) [Fintype α] [Fintype β]
        (μ : FinitePrior α) (ν : α → FinitePrior β)
        (F G : α → β → AllowedFrequency (frequencyBound Bs BD Bz k L) l →
          Choices (l:=l) C → Choices (l:=l) C → ℂ),
      (∀ a, μ.mass a ≠ 0 → ∀ b, (ν a).mass b ≠ 0 → ∀ r c e,
        choicesMass C.sources _ _ l c ≠ 0 → choicesMass C.sources _ _ l e ≠ 0 →
        ‖F a b r c e-G a b r c e‖ ≤ pairedChoiceCompensation C c e *
          (30*Real.exp (-Real.exp (ScaleBudget.giant.target*L)))) →
      ‖μ.cmean (fun a => (ν a).cmean (fun b => ∑ r, choicesPairSum C (F a b r))) -
        μ.cmean (fun a => (ν a).cmean (fun b => ∑ r, choicesPairSum C (G a b r)))‖ ≤
        Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L : ℝ)) ∧
      ‖μ.cmean (fun a => (ν a).cmean (fun b => ∑ r, choicesPairSum C (F a b r))) -
        μ.cmean (fun a => (ν a).cmean (fun b => ∑ r, choicesPairSum C (G a b r)))‖ ≤
        Real.exp (-H*(bulkSize k L : ℝ)) := by
  filter_upwards [selected_choices_error_eventually d Bs BD Bz hk,
    HistorySelectedRootErrorBudget.selected_nested_root_error_eventually Bs BD Bz H hH hk]
    with L hchoices hroot
  intro E C hG hcl hcu hb hd l hl α β _ _ μ ν F G hFG
  have h := hroot l hl α β μ ν
    (fun a b r => choicesPairSum C (F a b r)-choicesPairSum C (G a b r)) (by
      intro a ha b hb' r
      exact hchoices E C hG hcl hcu hb hd l hl (F a b r) (G a b r)
        (hFG a ha b hb' r))
  simpa only [Finset.sum_sub_distrib, GiantCollisionError.cmean_sub_eq] using h

end Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage

end

end OAI
