import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalFamily
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentOption
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentPointValue

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
local instance universalAlignmentSumInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources
    (Template.initial (2*(bulkSize k L/2)) k) l p)
  (D : OuterData C p o) (hD : outerData? C p o=some D)
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

include hD

theorem symbolic_value_eq_matched_selectedValue :
    (withDensity (symbolicPatternFamily C outside (Equiv.refl _) (outerNonbulk C l p o)
      p D.blockDraw D.valid J w P Q hactual hl D.nonbulk_pos D.left_mass D.right_mass
      houtside hw hpos hcell) mixed).value b mixed (bulkSize k L/2) hprime hV =
    HistoryBulkActualGoodPrincipal.selectedValue C p o outside (Equiv.refl _) J w P Q
      hactual hl houtside hw hpos hcell hprime mixed b false hV := by
  let F := alignmentDensityFamily C p o D outside J w P Q hactual hl houtside hw hpos hcell mixed
  change F.value b mixed (bulkSize k L/2) hprime hV = _
  unfold SymbolicPatternFamily.value HistoryBulkActualGoodPrincipal.selectedValue
  apply Finset.sum_congr rfl
  intro i _
  have hfperm : F.permutation=Equiv.refl _ :=
    alignmentDensityFamily_permutation C p o D outside J w P Q hactual hl houtside hw hpos hcell mixed
  simp only [hfperm]
  rw [selectMatchedOuterReference_eq_map C p o outside (Equiv.refl _) J w P Q i
    hactual hl houtside hw hpos D hD]
  change _ = ((selectWitness C outside (Equiv.refl _) (outerNonbulk C l p o)
      (leftBlockDraws C p D.blockDraw D.valid) (rightBlockDraws C p D.blockDraw D.valid)
      J w P Q hactual hl D.nonbulk_pos D.left_mass D.right_mass houtside hw hpos i).map
      (fun r => (⟨D,r⟩ : MatchedSelectedOuter C p o outside (Equiv.refl _) J w P Q i))).elim 0
      (fun R => matchedPrincipalValue R hcell hprime b mixed hV)
  cases hs : selectWitness C outside (Equiv.refl _) (outerNonbulk C l p o)
      (leftBlockDraws C p D.blockDraw D.valid) (rightBlockDraws C p D.blockDraw D.valid)
      J w P Q hactual hl D.nonbulk_pos D.left_mass D.right_mass houtside hw hpos i with
  | none =>
    have hi : ¬(F.refs i).isSome := by
      dsimp only [F]
      rw [alignmentDensityFamily_refs]
      simp only [referenceFamily,hs,Option.map_none]
      change ¬(false = true)
      exact Bool.false_ne_true
    simp only [presentComplexValue,dite_eq_right hi,Option.map_none,Option.elim_none]
  | some r =>
    have hi : (F.refs i).isSome := by
      dsimp only [F]
      rw [alignmentDensityFamily_refs]
      simp only [referenceFamily,hs,Option.map_some]
      rfl
    rw [presentComplexValue,dite_eq_left hi]
    have ht := symbolic_present_term_eq_matchedValue C p o D outside J w P Q hactual hl
      houtside hw hpos hcell hprime ⟨i,hi⟩ b mixed hV
    simpa only [F,Option.map_some,Option.elim_some,alignmentMatchedOuter,presentWitness,hs,Option.get_some]
      using! ht

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
