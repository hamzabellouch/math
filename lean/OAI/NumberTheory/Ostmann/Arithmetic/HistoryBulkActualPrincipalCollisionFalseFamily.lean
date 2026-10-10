import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalPattern
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionFalseDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkFibreIntegralReplacementFrame HistoryBulkPrincipalSourceReindex
open HistoryPairKernelReplacement HistoryBulkActualGoodPrincipal
attribute [local instance] Classical.propDecidable
attribute [local instance] HistoryBulkActualGoodPrincipal.actualGoodPatternInternalDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _ : Bool=>C.giant) C.sources
    (Template.initial (2*(bulkSize k L/2)) k) l p)
  (outside : List ℕ) (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
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

theorem pattern_before_eq_selectedBulkFamilyNormal
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (corrected : Bool)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) :
    HistoryBulkPatternIntegralReplacement.familyValue false
      (selectedPatternFamily C p o outside σ J w P Q hactual hl houtside hw hpos hcell hprime)
      b corrected mixed hV =
      selectedBulkFamilyNormal C p o outside σ J w P Q hactual hl houtside hw hpos hcell hprime
        mixed b corrected hV := by
  unfold HistoryBulkPatternIntegralReplacement.familyValue selectedPatternFamily
    selectedBulkFamilyNormal
  rw [sum_extendCommonRootOption
    (α := HistoryBulkPatternIntegralReplacement.Reference C outside l p) (β := ℂ)
    (frequencyBound Bs BD Bz k L) l]
  apply Finset.sum_congr
    (ι := Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) rfl
  intro i _
  cases hr : selectMatchedOuterReference C p o outside σ J w P Q i hactual hl houtside hw hpos with
  | none => rfl
  | some R =>
    simp only [Option.map_some,Option.elim_some,HistoryBulkPatternIntegralReplacement.Reference.weight,
      one_mul,Bool.false_eq_true,ite_false]
    exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
