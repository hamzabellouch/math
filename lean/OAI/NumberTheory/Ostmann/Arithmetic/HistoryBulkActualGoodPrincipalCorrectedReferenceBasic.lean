import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualCorrectedReferenceFamilyBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterData

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualRootReferenceFamily HistoryBulkSourceDisintegration
open HistoryBulkIndependentFibreReference
attribute [local instance] Classical.propDecidable
local instance actualGoodCorrectedReferenceBasicInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
  (outside : List ℕ) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))

structure CorrectedSelectedOuter where
  data : OuterData C p o
  witness : HistoryBulkActualCorrectedReferenceFamily.Witness C outside
    (outerNonbulk C l p o) e i.1.val i.1.val
    (leftChoices C (leftBlockDraws C p data.blockDraw data.valid) i)
    (rightChoices C (rightBlockDraws C p data.blockDraw data.valid) i)

def selectCorrectedOuterReference : Option (CorrectedSelectedOuter C p o outside e i) :=
  match outerData? C p o with
  | none => none
  | some D => (HistoryBulkActualCorrectedReferenceFamily.selectWitness C outside
      (outerNonbulk C l p o) e i.1.val i.1.val
      (leftChoices C (leftBlockDraws C p D.blockDraw D.valid) i)
      (rightChoices C (rightBlockDraws C p D.blockDraw D.valid) i)
      D.nonbulk_pos).map (fun r=>⟨D,r⟩)

theorem selectCorrectedOuterReference_eq_map (D : OuterData C p o)
    (hD : outerData? C p o=some D) :
    selectCorrectedOuterReference C p o outside e i=
      (HistoryBulkActualCorrectedReferenceFamily.selectWitness C outside
        (outerNonbulk C l p o) e i.1.val i.1.val
        (leftChoices C (leftBlockDraws C p D.blockDraw D.valid) i)
        (rightChoices C (rightBlockDraws C p D.blockDraw D.valid) i)
        D.nonbulk_pos).map (fun r=>⟨D,r⟩) := by
  unfold selectCorrectedOuterReference
  rw [hD]

theorem selectCorrectedOuterReference_none_iff (D : OuterData C p o)
    (hD : outerData? C p o=some D) :
    selectCorrectedOuterReference C p o outside e i=none ↔
      mixedFibreMean C outside (outerNonbulk C l p o) e i.1.val i.1.val
        (leftChoices C (leftBlockDraws C p D.blockDraw D.valid) i)
        (rightChoices C (rightBlockDraws C p D.blockDraw D.valid) i)=0 := by
  rw [selectCorrectedOuterReference_eq_map C p o outside e i D hD,Option.map_eq_none_iff]
  exact HistoryBulkActualCorrectedReferenceFamily.selectWitness_none_iff C outside
    (outerNonbulk C l p o) e i.1.val i.1.val
    (leftChoices C (leftBlockDraws C p D.blockDraw D.valid) i)
    (rightChoices C (rightBlockDraws C p D.blockDraw D.valid) i) D.nonbulk_pos

end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
