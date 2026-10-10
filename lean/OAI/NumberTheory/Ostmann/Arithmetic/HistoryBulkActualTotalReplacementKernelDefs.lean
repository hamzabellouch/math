import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageSelectedLawsBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementStageData

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily
open HistoryBulkActualBSquareReplacement HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualPrincipalKernelStage
attribute [local instance] Classical.propDecidable
local instance totalKernelInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

def plainKernelValue (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (hl : l≤k)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (mixed symbolic : Bool) (ds : Fin (2*(bulkSize k L/2)) → spectator.Sample) : ℂ :=
  if mixed then
    ∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),∑p,
      mixedKernelMean C p (spectatorList spectator ds) σ
        (fun o => plainMixedLawMultiplier C (spectatorList spectator ds)
          (outerGiants C l p o,outerNonbulk C l p o))
        D.reference hl
        (fun _q hq => (List.mem_ofFn.mp hq).elim (fun i hi => ⟨ds i,hi⟩))
        List.length_ofFn (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
        (D.residues ds) i.1 i.2.1 i.2.2 symbolic
  else
    ∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),∑p,
      primeKernelMean C p (spectatorList spectator ds) σ
        (fun o => primeLawMultiplier C (outerGiants C l p o,outerNonbulk C l p o))
        D.reference hl
        (fun _q hq => (List.mem_ofFn.mp hq).elim (fun i hi => ⟨ds i,hi⟩))
        List.length_ofFn (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
        (D.residues ds) i.1 i.2.1 i.2.2 symbolic

def plainKernelAverage (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (hl : l≤k)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) (mixed symbolic : Bool) : ℂ :=
  (spectatorPrior spectator (2*(bulkSize k L/2))).cmean
    (plainKernelValue C spectator D hl σ mixed symbolic)

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
