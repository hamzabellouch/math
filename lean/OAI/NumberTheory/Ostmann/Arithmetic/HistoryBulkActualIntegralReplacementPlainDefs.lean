import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalPlain
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPatternIntegralReplacementBackground
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSelectedInputs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualIntegralReplacement
open Construction Conclusion Filter
open HistoryBulkSourceDisintegration HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualGoodPrincipal HistoryBulkPatternIntegralReplacement
open HistoryBulkSupportConverse
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

def plainBulkPrincipal (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (ds : Fin (2*(bulkSize k L/2)) → spectator.Sample)
    (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
    (hl : l ≤ k) (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2)))) (mixed : Bool)
    (hV : ∀q∈spectatorList spectator ds,∀j ≤ l,frequencyBound Bs BD Bz k L j<q) : ℂ :=
  backgroundValue false (fun bg p b=>plainPatternFamily C spectator ds hactual hl σ mixed p
    (restoreOuterBackground C l p bg b)) false mixed hV

end Ostmann.Arithmetic.HistoryBulkActualIntegralReplacement

end

end OAI
