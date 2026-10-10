import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageSelectedLawsBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFixedReferenceTermSelected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily
open HistoryBulkActualBSquareReplacement HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualPrincipalKernelStage
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

def plainKernelSourceValue (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator) (hl : l≤k)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (mixed : Bool) (ds : Fin (2*(bulkSize k L/2)) → spectator.Sample)
    (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q) : ℂ :=
  if mixed then
    ∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),∑p,
      mixedKernelMean C p (spectatorList spectator ds) σ
        (fun o => plainMixedLawMultiplier C (spectatorList spectator ds)
          (outerGiants C l p o,outerNonbulk C l p o))
        hactual hl
        (fun _q hq => (List.mem_ofFn.mp hq).elim (fun i hi => ⟨ds i,hi⟩))
        List.length_ofFn (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
        hV i.1 i.2.1 i.2.2 true
  else
    ∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),∑p,
      primeKernelMean C p (spectatorList spectator ds) σ
        (fun o => primeLawMultiplier C (outerGiants C l p o,outerNonbulk C l p o))
        hactual hl
        (fun _q hq => (List.mem_ofFn.mp hq).elim (fun i hi => ⟨ds i,hi⟩))
        List.length_ofFn (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
        hV i.1 i.2.1 i.2.2 true

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
