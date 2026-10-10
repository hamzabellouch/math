import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamilyFactory
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatchedDensityBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkIndependentFibreReference
open HistoryBulkActualPrincipalBlockFamily HistoryBulkActualGoodPrincipal
open HistoryBulkPrincipalKernelReplacementMatched
attribute [local instance] Classical.propDecidable
local instance actualCorrectedPrincipalDensityInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)(outside : List ℕ)
  (e : RemainingPermutation (k:=k) (L:=L) (l:=l))(he : PreservesRemainingBands _ e)
  (n : ℕ)(hlen : outside.length=2*n)(hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

def correctedDensitySources
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l)
    (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l) :
    DensitySources (correctedPrincipalFamily (l:=l) C p outside e he n hlen hprime hV v f g) :=
  fun o ho=>(((selectCorrectedOuterReference C p o outside e (v,f,g)).get ho).frame he hprime).leftSource

def correctedDensityKernelError
    (mask : (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l) →
      (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l) →
      (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) →
      OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p → Prop) : ℝ :=
  ∑v,∑f,∑g,∑p,‖densityPrincipalDifferenceMean
    (correctedPrincipalFamily (l:=l) C p outside e he n hlen hprime hV v f g)
    (correctedDensitySources (l:=l) C outside e he n hlen hprime hV p v f g)
    true true (mask v f g p)‖

end Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamily

end

end OAI
