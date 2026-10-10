import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalPattern

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkSourceDisintegration
open HistoryBulkUniversalPatternAggregation HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualRootReferenceFamily HistoryBulkReferenceFrequencyFamily
open HistoryBulkSelectedUniversalOperator
attribute [local instance] Classical.propDecidable
local instance universalAlignmentAbsentInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources
    (Template.initial (2*(bulkSize k L/2)) k) l p)
  (hD : outerData? C p o=none)
  (outside : List ℕ)
  (J : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l → SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {α : Type} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
  {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (houtside : ∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q)
  (hw : ∀r,0≤w r) (hpos : ∀r,w r≠0 → 0<P r ∧ 0<Q r)
  (hcell : ∀r,w r≠0 → 0<P r ∧ 0<Q r ∧
    |Real.log (P r:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q r:ℝ)-(C.giantCenter:ℝ)|≤1)
  (hprime : ∀q∈outside,q.Prime) (mixed : Bool)
  (b : Block p → CommonSample C.sources
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

include hD in
theorem matched_pattern_value_eq_zero_of_none :
    HistoryBulkPatternIntegralReplacement.familyValue true
      (HistoryBulkActualGoodPrincipal.selectedPatternFamily C p o outside (Equiv.refl _)
        J w P Q hactual hl houtside hw hpos hcell hprime)
      b false mixed hV = 0 := by
  rw [HistoryBulkActualGoodPrincipal.pattern_after_eq_selectedValue]
  unfold HistoryBulkActualGoodPrincipal.selectedValue
  apply Finset.sum_eq_zero
  intro i _
  simp only [selectMatchedOuterReference,hD,Option.elim_none]

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
