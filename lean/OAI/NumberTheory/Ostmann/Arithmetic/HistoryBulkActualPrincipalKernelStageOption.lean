import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageValue

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation
open HistoryBulkActualPrincipalBlockFamily HistoryBulkPrincipalKernelReplacementMatched
open HistoryBulkReferencePeriodicMeanSource HistoryBulkFibreOriginalReference
attribute [local instance] Classical.propDecidable
local instance kernelStageOptionInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (outside : List ℕ) (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (J : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p →
    Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {α : Type} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
  {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (houtside : ∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q)
  (hw : ∀r,0≤w r) (hpos : ∀r,w r≠0 → 0<P r ∧ 0<Q r)
  (hcell : ∀r,w r≠0 → 0<P r ∧ 0<Q r ∧
    |Real.log (P r:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q r:ℝ)-(C.giantCenter:ℝ)|≤1)
  (hlen : outside.length=2*(bulkSize k L/2)) (hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l)
  (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l)

def selectedKernelOptionValue
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (symbolic corrected mixed : Bool) (u : SelectedBulkSample C l) : ℂ :=
  (selectMatchedOuterReference C p o outside σ (J o) w P Q (v,f,g)
    hactual hl houtside hw hpos).elim 0
    (fun R=>R.kernelTerm hcell hlen hprime hV symbolic corrected mixed u)

theorem selectedKernelOptionValue_typed
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (symbolic corrected mixed : Bool) (u : SelectedBulkSample C l) :
    (if Function.Injective (fun q=>(blockType p q,outerBlocks C l p o q)) then
      selectedKernelOptionValue C p outside σ J w P Q hactual hl houtside hw hpos hcell
        hlen hprime hV v f g o symbolic corrected mixed u else 0) =
      selectedKernelOptionValue C p outside σ J w P Q hactual hl houtside hw hpos hcell
        hlen hprime hV v f g o symbolic corrected mixed u := by
  unfold selectedKernelOptionValue
  cases hr : selectMatchedOuterReference C p o outside σ (J o) w P Q (v,f,g)
    hactual hl houtside hw hpos with
  | none => simp only [Option.elim_none,ite_self]
  | some R => rw [ite_eq_left R.data.typed]

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage

end

end OAI
