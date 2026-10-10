import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionPlainMixedEstimate
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionPlainPrimeEstimate

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion Filter HistoryBulkFibreGiantErrorAverage

theorem selected_plainCollisionPrincipal_error_eventually
    (d : Decomposition) (Bs BD Bz H : ℝ) {k : ℕ}
    (hBs : 0≤Bs) (hH : 0≤H) (hk : 2≤k) :
    ∀ᶠ L : ℝ in atTop,plainErrorProperty d Bs BD Bz H k L :=
  @Filter.Eventually.mono ℝ
    (fun L => plainPrimeErrorProperty d Bs BD Bz H k L ∧ plainMixedErrorProperty d Bs BD Bz H k L)
    (plainErrorProperty d Bs BD Bz H k) atTop
    ((selected_plainPrimeCollisionPrincipal_error_eventually d Bs BD Bz H hBs hH hk).and
      (selected_plainMixedCollisionPrincipal_error_eventually d Bs BD Bz H hBs hH hk))
    (fun _ hh E C hG hGu hcl hcu hb hd spectator hspec hactual ds hds l hl σ mixed hV =>
      match mixed with
      | false => hh.1 E C hG hGu hcl hcu hb hd spectator hspec hactual ds hds l hl σ hV
      | true => hh.2 E C hG hGu hcl hcu hb hd spectator hspec hactual ds hds l hl σ hV)
end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
