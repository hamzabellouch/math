import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalFamily
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPatternIntegralReplacementBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkGoodPatternAggregation HistoryBulkGoodPatternPrincipalFrame
open HistoryBulkFibreIntegralReplacementFrame HistoryBulkPrincipalSourceReindex
open HistoryPairKernelReplacement
attribute [local instance] Classical.propDecidable
local instance actualGoodPatternInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _ : Bool=>C.giant) C.sources
    (Template.initial (2*(bulkSize k L/2)) k) l p)
  (outside : List ℕ) (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (hgood : ¬TransferBadArrangement σ)
  (J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
    SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {α : Type} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
  {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (houtside : ∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q)
  (hw : ∀r,0≤w r) (hpos : ∀r,w r≠0 → 0<P r ∧ 0<Q r)
  (hcell : ∀r,w r≠0 → 0<P r ∧ 0<Q r ∧
    |Real.log (P r:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q r:ℝ)-(C.giantCenter:ℝ)|≤1)
  (hprime : ∀q∈outside,q.Prime) (mixed : Bool)

def selectedPatternFamily : HistoryBulkPatternIntegralReplacement.Family C outside l p :=
  extendCommonRootOption (frequencyBound Bs BD Bz k L) l (fun i=>
    (selectMatchedOuterReference C p o outside σ J w P Q i
      hactual hl houtside hw hpos).map (fun R=> {
        frame := R.frame hcell hprime
        nonbulk := outerNonbulk C l p o
        permutation := σ
        representative := R.representative hcell hprime
        mask := 1
        mask_mem := ⟨zero_le_one,le_refl _⟩ }))

theorem pattern_after_eq_selectedValue
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (corrected : Bool)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) :
    HistoryBulkPatternIntegralReplacement.familyValue true
      (selectedPatternFamily C p o outside σ J w P Q hactual hl houtside hw hpos hcell hprime)
      b corrected mixed hV=
      selectedValue C p o outside σ J w P Q hactual hl houtside hw hpos hcell hprime mixed b corrected hV := by
  unfold HistoryBulkPatternIntegralReplacement.familyValue selectedPatternFamily
  rw [sum_extendCommonRootOption]
  apply Finset.sum_congr rfl
  intro i _
  cases hr : selectMatchedOuterReference C p o outside σ J w P Q i hactual hl houtside hw hpos with
  | none => rfl
  | some R =>
    simp only [Option.map_some,Option.elim_some,HistoryBulkPatternIntegralReplacement.Reference.weight,
      one_mul,ite_true]
    exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm

theorem pattern_after_eq_goodFamily
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (corrected : Bool)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) :
    HistoryBulkPatternIntegralReplacement.familyValue true
      (selectedPatternFamily C p o outside σ J w P Q hactual hl houtside hw hpos hcell hprime)
      b corrected mixed hV=
    familyValue (selectedFamily C p o outside σ hgood J w P Q hactual hl houtside hw hpos
      hcell hprime mixed) b corrected mixed hV :=
  (pattern_after_eq_selectedValue C p o outside σ J w P Q hactual hl houtside hw hpos hcell hprime
    mixed b corrected hV).trans
    (familyValue_selectedFamily C p o outside σ hgood J w P Q hactual hl houtside hw hpos
      hcell hprime mixed b corrected hV).symm

end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
