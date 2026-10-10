import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementOriginalDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainGiantDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageActualMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageActualPrime
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageSelectedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageSourceMean

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantErrorAverage
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem selected_plain_giant_stage_eventually (d : Decomposition) (Bs BD Bz H : ℝ)
    {k : ℕ} (hBs : 0 ≤ Bs) (hH : 0 ≤ H) (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ spectator : PrimeSource,
      (∀ p : spectator.Sample, Real.exp ((1/2000:ℝ)*L) ≤ Real.log (p:ℕ) ∧
        Real.log (p:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ∃ hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator,
      ∀ (l : ℕ) (hl : l ≤ k)
        (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) (mixed : Bool),
      ‖plainOriginalAverage C spectator σ mixed-plainGiantAverage C spectator hactual hl σ mixed‖ ≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      ‖plainOriginalAverage C spectator σ mixed-plainGiantAverage C spectator hactual hl σ mixed‖ ≤
          Real.exp (-H*(bulkSize k L:ℝ)) := by
  filter_upwards [actual_prime_error_eventually d Bs BD Bz H hBs hH
      (lt_of_lt_of_le (Nat.zero_lt_succ 1) hk),
    actual_mixed_error_eventually d Bs BD Bz H hBs hH
      (lt_of_lt_of_le (Nat.zero_lt_succ 1) hk)] with L hp hm
  intro E C hG hGu hcl hcu hb hd spectator hspec
  obtain ⟨hactual,hp⟩ := hp E C hG hGu hcl hcu hb hd spectator hspec
  obtain ⟨hactual',hm⟩ := hm E C hG hGu hcl hcu hb hd spectator hspec
  refine ⟨hactual,fun l hl σ mixed => ?_⟩
  cases mixed
  · exact hp l hl σ
  · exact hm l hl σ

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
