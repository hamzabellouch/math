import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalCorrectedReferenceBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionCorrectedSource

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily HistoryBulkReferenceFrequencyFamily
open HistoryBulkFibreGiantErrorAverage HistoryBulkPrincipalSourceReindexWitness
open HistoryBulkActualPrincipalBlockFamily HistoryPairReferenceFlagExpectation
open HistoryBulkActualPrincipalSourceReindexPattern HistoryBulkActualPrincipalSourceReindexCompensation
open HistoryBulkActualGoodPrincipal HistoryBulkIndependentFibreReference
open HistoryBulkFibreOriginalReference
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
  (spectator : PrimeSource)
  (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands _ e)
  (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
  (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l)

theorem correctedSelector_map (D : OuterData C p o) (hD : outerData? C p o=some D) :
    (HistoryBulkActualCorrectedReferenceFamily.selectWitness C (spectatorList spectator ds)
      (outerNonbulk C l p o) e i.1.val i.1.val
      (leftChoices C (leftBlockDraws C p D.blockDraw D.valid) i)
      (rightChoices C (rightBlockDraws C p D.blockDraw D.valid) i) D.nonbulk_pos).map
      (fun r=>(⟨D,r⟩ : CorrectedSelectedOuter C p o (spectatorList spectator ds) e i))=
      selectCorrectedOuterReference C p o (spectatorList spectator ds) e i :=
  (selectCorrectedOuterReference_eq_map (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz)
    (L:=L) (k:=k) (l:=l) (E:=E) C p o
    (spectatorList spectator ds) e i D hD).symm

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption

end

end OAI
