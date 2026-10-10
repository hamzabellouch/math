import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexMatchedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionMap
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionMixedConstructor
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionMixedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionMixedSelector
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionMixedSource

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
open HistoryGiantReferenceMean HistoryBulkFibreGiantApproximationReference
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)

variable (spectator : PrimeSource)
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
  (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
  (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l)

theorem mixed_patternValue_eq_rawOption_of_outerData
    (D : OuterData C p o) (hD : outerData? C p o=some D) :
    drawPatternValue C spectator (mixedSelectedPrincipal C spectator hactual hl σ)
      ds (outerNonbulk C l p o) i p (outerBlocks C l p o)=
      mixedRawOption C p o spectator hactual hl σ ds i :=
  let W := Witness C (spectatorList spectator ds) σ (outerNonbulk C l p o)
    (leftBlockDraws C p D.blockDraw D.valid) (rightBlockDraws C p D.blockDraw D.valid)
    (fun i=>@HistoryBulkFibreGiantApproximation.plainMixedWeight d Bs BD Bz L k l E C (spectatorList spectator ds) (outerNonbulk C l p o) i.1.val) (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) i
  let T := MatchedSelectedOuter C p o (spectatorList spectator ds) σ
    (fun i=>@HistoryBulkFibreGiantApproximation.plainMixedWeight d Bs BD Bz L k l E C (spectatorList spectator ds) (outerNonbulk C l p o) i.1.val) (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) i
  let S : Option W := selectWitness C (spectatorList spectator ds) σ (outerNonbulk C l p o)
    (leftBlockDraws C p D.blockDraw D.valid) (rightBlockDraws C p D.blockDraw D.valid)
    (fun i=>@HistoryBulkFibreGiantApproximation.plainMixedWeight d Bs BD Bz L k l E C (spectatorList spectator ds) (outerNonbulk C l p o) i.1.val) (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant)
    hactual hl D.nonbulk_pos D.left_mass D.right_mass
    (spectatorList_source spectator ds) (mixedWeight_nonneg C.giantCenter C.giant)
    (fun r _=>mixedDraw_positive C.giantCenter C.giant r) i
  let S' : Option T := selectMatchedOuterReference C p o (spectatorList spectator ds) σ
    (fun i=>@HistoryBulkFibreGiantApproximation.plainMixedWeight d Bs BD Bz L k l E C (spectatorList spectator ds) (outerNonbulk C l p o) i.1.val) (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) i hactual hl
    (spectatorList_source spectator ds) (mixedWeight_nonneg C.giantCenter C.giant)
    (fun r _=>mixedDraw_positive C.giantCenter C.giant r)
  let mk : W→T := fun r=>⟨D,r⟩
  let g : W→ℂ := fun r=>mixedWitnessPrincipal C (spectatorList spectator ds) σ (outerNonbulk C l p o)
    (leftBlockDraws C p D.blockDraw D.valid) (rightBlockDraws C p D.blockDraw D.valid)
    r D.nonbulk_pos (D.left_mass i) (D.right_mass i)
    (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
  let h : T→ℂ := fun R=>(selectedBulkPrior C l).cmean (R.rawBTerm
    (fun v hv=>mixed_draw_cells C v (lt_of_le_of_ne (mixedWeight_nonneg C.giantCenter C.giant v) (Ne.symm hv)))
    (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) false true)
  (@mixedOuterPattern_eq_option d Bs BD Bz L k l E C p o spectator hactual hl σ ds i D).trans
    (@option_div_of_map W T S S' mk g h (blockJacobian C p D.blockDraw)
      (@mixed_constructor_div d Bs BD Bz L k l E C p o spectator σ ds i D)
      (@mixedSelector_map d Bs BD Bz L k l E C p o spectator hactual hl σ ds i D hD))

theorem mixed_patternValue_eq_rawOption
    (ho : outerMass C l p o≠0)
    (ht : Function.Injective (fun q=>(blockType p q,outerBlocks C l p o q))) :
    drawPatternValue C spectator (mixedSelectedPrincipal C spectator hactual hl σ)
      ds (outerNonbulk C l p o) i p (outerBlocks C l p o)=
      mixedRawOption C p o spectator hactual hl σ ds i :=
  Exists.elim (@exists_outerData_eq_some d Bs BD Bz L k l E C p o ho ht)
    (fun D hD=>@mixed_patternValue_eq_rawOption_of_outerData d Bs BD Bz L k l E C p o
      spectator hactual hl σ ds i D hD)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption

end

end OAI
