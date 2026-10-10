import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageCompensation
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantOriginalMeanChoicesDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage
open Construction Conclusion Filter HistoryGiantOriginalMeanFactorization

theorem selected_choices_error_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20 : ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter : ℝ) →
      (C.giantCenter : ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin : ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin : ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ l ≤ k, ∀ (F G : Choices (l:=l) C → Choices (l:=l) C → ℂ),
      (∀ c e, choicesMass C.sources _ _ l c ≠ 0 → choicesMass C.sources _ _ l e ≠ 0 →
        ‖F c e-G c e‖ ≤ pairedChoiceCompensation C c e *
          (30*Real.exp (-Real.exp (ScaleBudget.giant.target*L)))) →
      ‖choicesPairSum C F-choicesPairSum C G‖ ≤
        Real.exp (-Real.exp ((21/2000 : ℝ)*L)) := by
  filter_upwards [selected_pairedChoiceCompensation_error_eventually d Bs BD Bz hk] with L hL
  intro E C hG hcl hcu hb hd l hl F G hFG
  exact (choicesPairSum_error_le C F G
    (fun c e => pairedChoiceCompensation C c e *
      (30*Real.exp (-Real.exp (ScaleBudget.giant.target*L)))) hFG).trans
    (hL E C hG hcl hcu hb hd l hl)

end Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage

end

end OAI
