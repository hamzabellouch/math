import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamilyDensity

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
open HistoryBulkPrincipalKernelReplacementMatched Filter
attribute [local instance] Classical.propDecidable
local instance actualCorrectedPrincipalDensityStatementInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

def SelectedCorrectedDensityKernelEstimate
    (d : Decomposition) (Bs BD Bz D H : ℝ) (k : ℕ) : Prop :=
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀q:spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (q:ℕ) ∧
        Real.log (q:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∀outside : List ℕ,(∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q) →
      ∀(n : ℕ)(hlen : outside.length=2*n),outside.length≤bulkSize k L →
      ∀(l : ℕ), l<k →
      ∀(e : RemainingPermutation (k:=k) (L:=L) (l:=l))(he : PreservesRemainingBands (Template.remainder (l+1)
        (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) e),
      ∃(hprime : ∀q∈outside,q.Prime)
        (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q),
      ∀mask : (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l) →
        (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l) →
        (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) →
        OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p → Prop,
      Real.exp (D*(L+1)^2)*@correctedDensityKernelError d Bs BD Bz L k l E C outside e he n hlen hprime hV mask≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      Real.exp (D*(L+1)^2)*@correctedDensityKernelError d Bs BD Bz L k l E C outside e he n hlen hprime hV mask≤
          Real.exp (-H*(bulkSize k L:ℝ))

end Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamily

end

end OAI
