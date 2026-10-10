import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainInitialMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainInitialPrime

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem plainGiantAverage_eq_plainSquareAverage
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (hl : l ≤ k)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) (mixed : Bool) :
    plainGiantAverage (l:=l) C spectator D.reference hl σ mixed =
      plainSquareAverage (l:=l) C spectator D hl σ mixed false := by
  cases mixed
  · exact plainGiantAverage_eq_plainSquareAverage_prime C spectator D hl σ
  · exact plainGiantAverage_eq_plainSquareAverage_mixed C spectator D hl σ

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
