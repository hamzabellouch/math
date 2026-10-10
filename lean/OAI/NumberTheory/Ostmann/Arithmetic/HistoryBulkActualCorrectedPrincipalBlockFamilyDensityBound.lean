import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamilyDensityExpression

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
local instance actualCorrectedPrincipalDensityBoundInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)(outside : List ℕ)
  (e : RemainingPermutation (k:=k) (L:=L) (l:=l))(he : PreservesRemainingBands _ e)
  (n : ℕ)(hlen : outside.length=2*n)(hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem correctedDensityKernelError_bound (a r₁ r₂ : ℝ)
    (h : ∀(F : AllowedFrequency (frequencyBound Bs BD Bz k L) l →
      (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l) →
      (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) →
      MatchedPrincipalBlockFamily C outside l f g p),
      (∀v f g p o ho,HistoryPairPattern.RootGiantsAgree
        ((F v f g p).reference o ho).left.history ((F v f g p).reference o ho).right.history) →
      ∀(X : ∀v f g p,DensitySources (F v f g p))
      (mask : AllowedFrequency (frequencyBound Bs BD Bz k L) l →
        FrequencyChoices (frequencyBound Bs BD Bz k L) l →
        FrequencyChoices (frequencyBound Bs BD Bz k L) l →
        (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) →
        OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p → Prop),
      a*(∑v,∑f,∑g,∑p,‖densityPrincipalDifferenceMean (F v f g p) (X v f g p) true true (mask v f g p)‖)≤r₁ ∧
      a*(∑v,∑f,∑g,∑p,‖densityPrincipalDifferenceMean (F v f g p) (X v f g p) true true (mask v f g p)‖)≤r₂)
    (mask : AllowedFrequency (frequencyBound Bs BD Bz k L) l →
      FrequencyChoices (frequencyBound Bs BD Bz k L) l →
      FrequencyChoices (frequencyBound Bs BD Bz k L) l →
      (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) →
      OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p → Prop) :
    a*correctedDensityKernelError (l:=l) C outside e he n hlen hprime hV mask≤r₁ ∧
    a*correctedDensityKernelError (l:=l) C outside e he n hlen hprime hV mask≤r₂ := by
  rw [correctedDensityKernelError_eq]
  exact h
    (fun v f g p=>correctedPrincipalFamily (l:=l) C p outside e he n hlen hprime hV v f g)
    (fun v f g p o ho=>correctedPrincipalFamily_reference_giants (l:=l) C p outside e he n hlen hprime hV v f g o ho)
    (fun v f g p=>correctedDensitySources (l:=l) C outside e he n hlen hprime hV p v f g) mask

end Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamily

end

end OAI
