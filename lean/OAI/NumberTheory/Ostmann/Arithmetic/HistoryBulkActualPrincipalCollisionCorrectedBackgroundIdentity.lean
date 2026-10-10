import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualIntegralReplacementCorrectedDefsBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedBackgroundDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedFalse

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected
attribute [local instance] Classical.propDecidable
open Construction Conclusion HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily
open HistoryBulkIndependentFibreReference HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualIntegralReplacement HistoryBulkPatternIntegralReplacement
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem selectedBackgroundMean_false_eq_correctedBulkPrincipal
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (ds : Fin (2*(bulkSize k L/2))→spectator.Sample) (hl : l<k)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) (he : PreservesRemainingBands _ e)
    (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q) :
    selectedBackgroundMean (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C (spectatorList spectator ds) e he List.length_ofFn
      (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) hV false=
      correctedBulkPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C spectator ds hl e he hV :=
  FinitePrior.cmean_congr_support (backgroundPrior C l) _ _ (fun bg _=>
    selectedCollisionMean_false_eq_pattern (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
      C (spectatorList spectator ds) e he List.length_ofFn
      (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) hV bg true true)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected

end

end OAI
