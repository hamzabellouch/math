import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalComparisonPrincipalStatement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalActual
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentMeanFinal

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalComparison
open Construction Conclusion Filter HistoryBulkActualTotalReplacement HistoryBulkSourceDisintegration
open HistoryBulkActualUniversalPrincipal

private theorem two_hundred_nonnegative : (0:ℝ) ≤ 200 := by norm_num
private theorem nine_nonnegative : (0:ℝ) ≤ 9 := by norm_num

theorem actual_plainFinal_eventually (d : Decomposition) (BD Bz : ℝ)
    (hBD : 0≤BD) (hBz : 9≤Bz) (k : ℕ) (hk : 2≤k) :
    ActualPlainFinalEstimate d BD Bz k :=
  (actual_principal_eventually d 200 BD Bz two_hundred_nonnegative hBD
    (le_trans nine_nonnegative hBz) hk).mono
    (fun L hL P hP hZ E C hsource =>
      let ⟨hactual, hbound⟩ := hL E C hsource.block_lower hsource.block_upper
        hsource.center_lower hsource.center_upper hsource.bulk_bin hsource.spectator_bin
        (harmonicPrimeSource P hP hZ) (fun p => hsource.band p.val p.property)
      ⟨hactual, fun l hl =>
        let ⟨hV, hmain⟩ := hbound l hl
        ⟨hV, fun mixed =>
          (congrArg norm (replacementMean_eq_plainFinalAverage
            (d:=d) (Bs:=200) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
            C (harmonicPrimeSource P hP hZ) hactual hl
            (spectator_membership (harmonicPrimeSource P hP hZ)) mixed hV)).symm.trans_le
              (hmain mixed)⟩⟩)

end Ostmann.Arithmetic.HistoryBulkActualUniversalComparison

end

end OAI
