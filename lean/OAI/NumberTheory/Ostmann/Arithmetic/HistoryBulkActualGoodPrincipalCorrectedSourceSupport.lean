import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalCorrectedSourceSupportCoordinates
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterMass
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentFibreReferenceMean

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualRootReferenceFamily HistoryBulkSourceDisintegration
open HistoryBulkIndependentFibreReference HistoryPairKernelProductReplacement
attribute [local instance] Classical.propDecidable
local instance actualGoodCorrectedSourceSupportInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ} {e : RemainingPermutation (k:=k) (L:=L) (l:=l)}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}
namespace CorrectedSelectedOuter
variable (R : CorrectedSelectedOuter C p o outside e i)
  (he : PreservesRemainingBands _ e)
  (y : OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
  (ho : originalDrawOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p y = o)
  (hm : originalDrawMass (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p y ≠ 0)

include ho hm

theorem rightRootSupported_originalDraw :
    RightRootSupported (R.blockReference he) (fun _=>C.giant) y := by
  have hu := ((originalDrawMass_ne_zero_iff C l p y).mp hm).2
  let hc := reference_compatible_all C outside (outerNonbulk C l p o) e he i.1.val i.1.val
    (leftChoices C (leftBlockDraws C p R.data.blockDraw R.data.valid) i)
    (rightChoices C (rightBlockDraws C p R.data.blockDraw R.data.valid) i)
    R.witness (originalDrawBulk C l p y)
  have hmass := reference_right_mass_nonzero C outside (outerNonbulk C l p o) e he i.1.val i.1.val
    (leftChoices C (leftBlockDraws C p R.data.blockDraw R.data.valid) i)
    (rightChoices C (rightBlockDraws C p R.data.blockDraw R.data.valid) i)
    R.witness (originalDrawBulk C l p y) hc hu
  apply rightRootSupported_of_assignment (R.blockReference he) (fun _=>C.giant) y
    (rightAssignment C (outerNonbulk C l p o) e (originalDrawBulk C l p y) hc) hmass
  exact R.matchedReferenceSample_right_assignment he y ho hc

theorem rightRootSupportIndicator_eq_one :
    rightRootSupportIndicator (R.blockReference he) (fun _=>C.giant) y = 1 := by
  unfold rightRootSupportIndicator
  exact ite_eq_left (R.rightRootSupported_originalDraw he y ho hm)

end CorrectedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
