import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamilyData
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyMatchedMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagPrincipalMatchedFamily

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkIndependentFibreReference
open HistoryBulkActualPrincipalBlockFamily HistoryBulkActualGoodPrincipal
open HistoryPairPattern HistoryDiagonalRemainingRootMatching
attribute [local instance] Classical.propDecidable
local instance actualCorrectedPrincipalFactoryInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (outside : List ℕ)(e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands _ e)
  (n : ℕ)(hlen : outside.length=2*n)(hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l)
  (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l)

def correctedPrincipalFamily : MatchedPrincipalBlockFamily C outside l f g p where
  active o := (selectCorrectedOuterReference C p o outside e (v,f,g)).isSome
  reference o ho := ((selectCorrectedOuterReference C p o outside e (v,f,g)).get ho).blockReference he
  leftRootFrequency := v.val
  rightRootFrequency := v.val
  leftRootFrequency_eq := fun _ _=>rfl
  rightRootFrequency_eq := fun _ _=>rfl
  leftFrequency_eq := fun _ _=>rfl
  rightFrequency_eq := fun _ _=>rfl
  permutation := fullPermutation (l+1) _ e he
  rootAligned o ho j := reference_rootAligned
    ((selectCorrectedOuterReference C p o outside e (v,f,g)).get ho) he j
  principal o ho := principalData ((selectCorrectedOuterReference C p o outside e (v,f,g)).get ho)
    he n hlen hprime hV

theorem correctedPrincipalFamily_reference_giants
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (ho : (correctedPrincipalFamily C p outside e he n hlen hprime hV v f g).active o) :
    RootGiantsAgree
      ((correctedPrincipalFamily C p outside e he n hlen hprime hV v f g).reference o ho).left.history
      ((correctedPrincipalFamily C p outside e he n hlen hprime hV v f g).reference o ho).right.history :=
  reference_giants ((selectCorrectedOuterReference C p o outside e (v,f,g)).get ho) he

theorem correctedPrincipalFamily_mean_eq :
    (correctedPrincipalFamily C p outside e he n hlen hprime hV v f g).mean true true=
      matchedOuterPrincipalFlagMean
        (correctedPrincipalFamily C p outside e he n hlen hprime hV v f g) true true :=
  matched_mean_eq_outerPrincipalFlagMean _ true true

end Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamily

end

end OAI
