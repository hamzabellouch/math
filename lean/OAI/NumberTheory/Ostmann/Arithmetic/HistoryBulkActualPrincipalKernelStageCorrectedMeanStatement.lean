import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterEquivBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterMass
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedOption

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation HistoryBulkIndependentFibreReference
open HistoryBulkActualPrincipalBlockFamily HistoryBulkActualGoodPrincipal
open HistoryBulkActualCorrectedPrincipalBlockFamily HistoryBulkPrincipalKernelReplacementMatched
attribute [local instance] Classical.propDecidable
local instance correctedKernelMeanStatementInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (outside : List ℕ) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands (Template.remainder (l+1)
    (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) e)
  (hlen : outside.length=2*(bulkSize k L/2)) (hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l)
  (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l)

def JacobianOptionEquality
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (symbolic : Bool) (u : SelectedBulkSample C l)
    : Prop :=
    densityPrincipalProductTerm (C:=C) (l:=l) (outside:=outside) (f:=f) (g:=g) (p:=p) symbolic
      (correctedPrincipalFamily (l:=l) C p outside e he (bulkSize k L/2) hlen hprime hV v f g)
      (correctedDensitySources (l:=l) C outside e he (bulkSize k L/2) hlen hprime hV p v f g)
      true true (selectedKernelMask (l:=l) C p outside e he hprime v f g)
      (restoreOriginalDraw C l p o u) =
    (∏q : Block p,((outerBlocks C l p o q).val:ℂ))*
      selectedKernelOptionValue (l:=l) C p outside e he hlen hprime hV v f g o symbolic u

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
