import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionCorrectedMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionCorrectedSelector
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionCorrectedSource
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionMap

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

theorem corrected_patternValue_eq_rawOption_of_outerData
    (D : OuterData C p o) (hD : outerData? C p o=some D) :
    drawPatternValue C spectator (correctedSelectedPrincipal (l:=l) C spectator e he)
      ds (outerNonbulk C l p o) i p (outerBlocks C l p o)=
      (selectCorrectedOuterReference C p o (spectatorList spectator ds) e i).elim 0
        (fun R=>(selectedBulkPrior C l).cmean (R.rawBTerm he
          (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds))) :=
  let W := HistoryBulkActualCorrectedReferenceFamily.Witness C (spectatorList spectator ds)
    (outerNonbulk C l p o) e i.1.val i.1.val
    (leftChoices C (leftBlockDraws C p D.blockDraw D.valid) i)
    (rightChoices C (rightBlockDraws C p D.blockDraw D.valid) i)
  let T := CorrectedSelectedOuter C p o (spectatorList spectator ds) e i
  let S : Option W := HistoryBulkActualCorrectedReferenceFamily.selectWitness C
    (spectatorList spectator ds) (outerNonbulk C l p o) e i.1.val i.1.val
    (leftChoices C (leftBlockDraws C p D.blockDraw D.valid) i)
    (rightChoices C (rightBlockDraws C p D.blockDraw D.valid) i) D.nonbulk_pos
  let S' : Option T := selectCorrectedOuterReference C p o (spectatorList spectator ds) e i
  let mk : W→T := fun r=>⟨D,r⟩
  let g : W→ℂ := fun r=>correctedWitnessPrincipal C (spectatorList spectator ds)
    (outerNonbulk C l p o) e he i.1.val i.1.val
    (leftChoices C (leftBlockDraws C p D.blockDraw D.valid) i)
    (rightChoices C (rightBlockDraws C p D.blockDraw D.valid) i) r D.nonbulk_pos
    (D.left_mass i) (D.right_mass i)
    (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
  let h : T→ℂ := fun R=>
    (selectedBulkPrior C l).cmean (R.rawBTerm he
      (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds))
  (@correctedOuterPattern_eq_option d Bs BD Bz L k l E C p o spectator e he ds i D).trans
    (@option_div_of_map W T S S' mk g h (blockJacobian C p D.blockDraw)
      (@corrected_constructor_div d Bs BD Bz L k l E C p o spectator e he ds i D)
      (@correctedSelector_map d Bs BD Bz L k l E C p o spectator e ds i D hD))

theorem corrected_patternValue_eq_rawOption
    (ho : outerMass C l p o≠0)
    (ht : Function.Injective (fun q=>(blockType p q,outerBlocks C l p o q))) :
    drawPatternValue C spectator (correctedSelectedPrincipal (l:=l) C spectator e he)
      ds (outerNonbulk C l p o) i p (outerBlocks C l p o)=
      (selectCorrectedOuterReference C p o (spectatorList spectator ds) e i).elim 0
        (fun R=>(selectedBulkPrior C l).cmean (R.rawBTerm he
          (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds))) :=
  Exists.elim (@exists_outerData_eq_some d Bs BD Bz L k l E C p o ho ht)
    (fun D hD=>@corrected_patternValue_eq_rawOption_of_outerData d Bs BD Bz L k l E C p o spectator e he ds i D hD)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption

end

end OAI
