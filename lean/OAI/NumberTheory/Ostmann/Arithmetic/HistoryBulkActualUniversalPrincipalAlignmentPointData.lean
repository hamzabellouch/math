import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentPointFrame
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentPointRepresentative

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkReferenceFrequencyFamily HistoryBulkSelectedUniversalOperator
attribute [local instance] Classical.propDecidable
local instance actualUniversalPrincipalPointDataInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
  (D : OuterData C p o) (outside : List ℕ)
  (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
  (J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
    SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {α : Type} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
  {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (houtside : ∀q∈outside,∃v:spectator.Sample,(v:ℕ)=q)
  (hw : ∀v,0≤w v) (hpos : ∀v,w v≠0 → 0<P v ∧ 0<Q v)
  (hcell : ∀v,w v≠0 → 0<P v ∧ 0<Q v ∧
    |Real.log (P v:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q v:ℝ)-(C.giantCenter:ℝ)|≤1)
  (hprime : ∀q∈outside,q.Prime)
  (i : RootPresent (referenceFamily C outside σ (outerNonbulk C l p o)
    (leftBlockDraws C p D.blockDraw D.valid) (rightBlockDraws C p D.blockDraw D.valid)
    J w P Q hactual hl D.nonbulk_pos D.left_mass D.right_mass houtside hw hpos))

theorem frameOfData_reference_transport
    {x y : InternalSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l}
    {j : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l}
    {a b : SupportedReference C.sources (Template.initial (2*(bulkSize k L/2)) k)
      (frequencyBound Bs BD Bz k L) outside l x y j.1.val j.1.val j.2}
    (hab : a=b) (v : ActualReferenceData C σ j b) :
    frameOfData (Eq.mpr (congrArg (ActualReferenceData C σ j) hab) v) hprime=
      frameOfData v hprime := by
  cases hab
  rfl

theorem symbolic_data_frame_eq_present :
    frameOfData
      ((symbolicPatternFamily C outside σ (outerNonbulk C l p o) p D.blockDraw D.valid
        J w P Q hactual hl D.nonbulk_pos D.left_mass D.right_mass houtside hw hpos hcell).data i)
      hprime=
    (MatchedSelectedOuter.frame
      (⟨D,presentWitness C outside σ (outerNonbulk C l p o)
        (leftBlockDraws C p D.blockDraw D.valid) (rightBlockDraws C p D.blockDraw D.valid)
        J w P Q hactual hl D.nonbulk_pos D.left_mass D.right_mass houtside hw hpos i⟩ :
        MatchedSelectedOuter C p o outside σ J w P Q i.val) hcell hprime) := by
  change frameOfData
    (actualData C outside σ (outerNonbulk C l p o)
      (leftBlockDraws C p D.blockDraw D.valid) (rightBlockDraws C p D.blockDraw D.valid)
      J w P Q hactual hl D.nonbulk_pos D.left_mass D.right_mass houtside hw hpos hcell i) hprime=_
  unfold actualData
  rw [frameOfData_reference_transport (hab := rootSelected_eq_presentWitness C outside σ
    (outerNonbulk C l p o) (leftBlockDraws C p D.blockDraw D.valid)
    (rightBlockDraws C p D.blockDraw D.valid) J w P Q hactual hl
    D.nonbulk_pos D.left_mass D.right_mass houtside hw hpos i)]
  rfl

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
