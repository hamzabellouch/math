import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedBackgroundFinite
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedBackgroundProperty
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSelectedMaskBound

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryBulkActualRootReferenceFamily HistoryBulkIndependentFibreReference
open HistoryBulkActualPrincipalBlockFamily HistoryBulkActualPrincipalCollision

theorem selected_corrected_background_error_eventually
    (d : Decomposition) (Bs BD Bz H : ℝ) {k : ℕ}
    (hBs : 0≤Bs) (hH : 0≤H) (hk : 2≤k) :
    ∀ᶠ L : ℝ in atTop, correctedBackgroundErrorProperty d Bs BD Bz H k L :=
  @Filter.Eventually.mono ℝ
    (backgroundErrorProperty d Bs BD Bz H k)
    (correctedBackgroundErrorProperty d Bs BD Bz H k) atTop
    (selected_background_collision_error_eventually d Bs BD Bz H (k:=k) hBs hH hk)
    (fun L hL E C hG hGu hcl hcu hb hd spectator hspec ds hds l hl e he hV=>
      selectedBackgroundMean_error_le
        (ε := Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)))
        (θ := Real.exp (-H*(bulkSize k L:ℝ))) (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C (spectatorList spectator ds) e he List.length_ofFn
        (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) hV
        (hL E C hG hGu hcl hcu hb hd spectator hspec l true true hl
          (spectatorList spectator ds) (spectatorList_length_le (n:=bulkSize k L) spectator ds)
          (spectatorList_source_mass spectator ds hds)
          (selectedCollisionReferences (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C (spectatorList spectator ds) e he List.length_ofFn
            (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) hV)
          (fun bg i=>selectedCollisionMask (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C (spectatorList spectator ds) e he
            (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) bg i true)
          (fun bg i u p b=>selectedCollisionMask_mem (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C (spectatorList spectator ds) e he
            (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) bg i true u p b)))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected

end

end OAI
