import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainGiantDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementSquareDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkActualPrincipalSourceReindex
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem plainGiantAverage_eq_plainSquareAverage_mixed
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (hl : l ≤ k)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) :
    plainGiantAverage (l:=l) C spectator D.reference hl σ true =
      plainSquareAverage (l:=l) C spectator D hl σ true false :=
  original_mixed_principal_eq_B_sourceMean (l:=l) C spectator D.reference hl σ
    D.admissible D.residues D.frequencies

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
