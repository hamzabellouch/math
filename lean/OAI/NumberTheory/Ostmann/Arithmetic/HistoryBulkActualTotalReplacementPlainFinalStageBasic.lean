import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualIntegralReplacementPlainDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainBulkDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkActualIntegralReplacement HistoryBulkActualGoodPrincipal
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem plain_final_stage_average_bound
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
    (hl : l ≤ k) (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) (mixed : Bool)
    (hV : SpectatorResidueBounds C spectator l) (B D : ℝ)
    (h : ∀ ds, ‖plainBulkPrincipal C spectator ds hactual hl σ mixed (hV ds)-
          plainPrincipal C spectator ds hactual hl σ mixed (hV ds)‖ ≤ B ∧
        ‖plainBulkPrincipal C spectator ds hactual hl σ mixed (hV ds)-
          plainPrincipal C spectator ds hactual hl σ mixed (hV ds)‖ ≤ D) :
    ‖plainBulkAverage C spectator hactual hl σ mixed hV-
      plainFinalAverage C spectator hactual hl σ mixed hV‖ ≤ B ∧
    ‖plainBulkAverage C spectator hactual hl σ mixed hV-
      plainFinalAverage C spectator hactual hl σ mixed hV‖ ≤ D :=
  norm_cmean_sub_le_both (spectatorPrior spectator (2*(bulkSize k L/2)))
    (fun ds => plainBulkPrincipal C spectator ds hactual hl σ mixed (hV ds))
    (fun ds => plainPrincipal C spectator ds hactual hl σ mixed (hV ds)) B D (fun ds _ => h ds)

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
