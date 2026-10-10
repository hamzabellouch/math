import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyMatchedFactory
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatchedDensityBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSourceScalar

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
local instance kernelStageDefsInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
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

def selectedKernelDensitySources : DensitySources
    (matchedPrincipalFamily C p outside σ J w P Q hactual hl houtside hw hpos hcell
      (bulkSize k L/2) hlen hprime hV true v f g) := fun o ho=>
  ((selectMatchedOuterReference C p o outside σ (J o) w P Q (v,f,g)
    hactual hl houtside hw hpos).get ho).frame hcell hprime |>.leftSource

def selectedKernelOuterMask
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (x : Frame.Source (C:=C) (l:=l)) : Prop :=
  match selectMatchedOuterReference C p o outside σ (J o) w P Q (v,f,g)
      hactual hl houtside hw hpos with
  | none => False
  | some R =>
    let r := R.frame hcell hprime
    ((r.newLeft x).root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime ∧
      ((r.newRight (permuteAssignment C σ x)).root.small.map SmallSlot.value++outside).Pairwise Nat.Coprime

def selectedKernelMask
    (y : OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p) : Prop :=
  selectedKernelOuterMask C p outside σ J w P Q hactual hl houtside hw hpos hcell hprime v f g
    (originalDrawOuter (fun _=>C.giant) C.sources _ l p y) (originalDrawAssignment C l p y)

def selectedKernelMean (symbolic corrected mixed : Bool) : ℂ :=
  densityPrincipalProductMean symbolic
    (matchedPrincipalFamily C p outside σ J w P Q hactual hl houtside hw hpos hcell
      (bulkSize k L/2) hlen hprime hV true v f g)
    (selectedKernelDensitySources C p outside σ J w P Q hactual hl houtside hw hpos hcell
      hlen hprime hV v f g)
    corrected mixed
    (selectedKernelMask C p outside σ J w P Q hactual hl houtside hw hpos hcell hprime v f g)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage

end

end OAI
