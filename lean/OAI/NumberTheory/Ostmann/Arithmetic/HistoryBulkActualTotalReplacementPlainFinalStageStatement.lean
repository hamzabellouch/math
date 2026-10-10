import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainBulkDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion Filter HistoryBulkSourceDisintegration

def PlainFinalStageEstimate (d : Decomposition) (Bs BD Bz H : ℝ) (k : ℕ) : Prop :=
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
      ∀ hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator,
      ∀ (l : ℕ) (hl : l ≤ k),
      ∀ hV : SpectatorResidueBounds C spectator l,
      ∀ (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) (mixed : Bool),
      ‖plainBulkAverage C spectator hactual hl σ mixed hV-
        plainFinalAverage C spectator hactual hl σ mixed hV‖ ≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      ‖plainBulkAverage C spectator hactual hl σ mixed hV-
        plainFinalAverage C spectator hactual hl σ mixed hV‖ ≤
          Real.exp (-H*(bulkSize k L:ℝ))

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
