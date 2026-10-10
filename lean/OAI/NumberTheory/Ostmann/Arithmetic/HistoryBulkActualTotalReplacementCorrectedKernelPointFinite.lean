import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedMeanScalarDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelEqualityFinite
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelPointValue

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion CanonicalOccurrenceTransport
open HistoryBulkActualRootReferenceFamily HistoryBulkIndependentFibreReference
open HistoryBulkActualPrincipalKernelStageCorrected
attribute [local instance] Classical.propDecidable
local instance kernelPointFiniteInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem correctedKernelValue_bounds (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (D : PlainStageData C spectator l) (hl : l<k)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) (he : PreservesRemainingBands _ e)
    (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
    (hp : ∀q∈spectatorList spectator ds,q.Prime)
    (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q)
    (r₁ r₂ : ℝ)
    (h : let f : Bool→ℂ := fun b=>
      ∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),∑p,
        selectedKernelMean (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
          (k:=k) (l:=l) (E:=E) C p (spectatorList spectator ds) e he List.length_ofFn hp hV
          i.1 i.2.1 i.2.2 b
      ‖f false-f true‖≤r₁ ∧ ‖f false-f true‖≤r₂) :
    ‖correctedKernelValue C spectator D hl e he false ds-
        correctedKernelValue C spectator D hl e he true ds‖≤r₁ ∧
    ‖correctedKernelValue C spectator D hl e he false ds-
        correctedKernelValue C spectator D hl e he true ds‖≤r₂ :=
  norm_sub_bounds_of_eq
    (correctedKernelValue_eq C spectator D hl e he ds hp hV false)
    (correctedKernelValue_eq C spectator D hl e he ds hp hV true) h

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
