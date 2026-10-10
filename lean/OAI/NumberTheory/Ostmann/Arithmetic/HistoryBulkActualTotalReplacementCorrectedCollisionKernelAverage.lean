import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkIndependentFibreReference
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem correctedKernelAverage_eq_guarded
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (hl : l<k)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) (symbolic : Bool) :
    correctedKernelAverage (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
      C spectator D hl e symbolic =
      if he : PreservesRemainingBands _ e then
        (spectatorPrior spectator (2*(bulkSize k L/2))).cmean
          (correctedKernelValue (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
            C spectator D hl e he symbolic)
      else 0 := by
  exact Eq.trans (Eq.refl _) (Eq.refl _)

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
