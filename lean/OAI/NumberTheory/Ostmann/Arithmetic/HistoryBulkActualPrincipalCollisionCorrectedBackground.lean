import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedBackgroundBound
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedBackgroundCanonicalFinite
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedBackgroundFinalProperty

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryBulkIndependentFibreReference HistoryBulkActualPrincipalCollision
open HistoryBulkActualIntegralReplacement

private theorem correctedCollisionProof
    (d : Decomposition) (Bs BD Bz H : ℝ) {k : ℕ}
    (hBs : 0≤Bs) (hH : 0≤H) (hk : 2≤k) :
    ∀ᶠ L : ℝ in atTop, correctedCollisionErrorProperty d Bs BD Bz H k L :=
  @Filter.Eventually.mono ℝ
    (correctedBackgroundErrorProperty d Bs BD Bz H k)
    (correctedCollisionErrorProperty d Bs BD Bz H k) atTop
    (selected_corrected_background_error_eventually d Bs BD Bz H (k:=k) hBs hH hk)
    (fun L hL E C hG hGu hcl hcu hb hd spectator hspec ds hds l hl e he hV=>
      correctedCollisionPrincipal_error_le
        (ε := Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)))
        (θ := Real.exp (-H*(bulkSize k L:ℝ)))
        (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
        C spectator ds hl e he hV
        (hL E C hG hGu hcl hcu hb hd spectator hspec ds hds l hl e he hV))

theorem selected_corrected_collision_error_eventually
    (d : Decomposition) (Bs BD Bz H : ℝ) {k : ℕ}
    (hBs : 0≤Bs) (hH : 0≤H) (hk : 2≤k) :
    ∀ᶠ L : ℝ in atTop, correctedCollisionErrorProperty d Bs BD Bz H k L :=
  correctedCollisionProof d Bs BD Bz H (k:=k) hBs hH hk

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected

end

end OAI
