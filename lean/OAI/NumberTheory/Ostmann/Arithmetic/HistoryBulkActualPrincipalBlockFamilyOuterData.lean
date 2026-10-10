import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuter
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyReference

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryPairSourceLaws
attribute [local instance] Classical.propDecidable
local instance actualPrincipalOuterDataInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)

structure OuterData : Type where
  typed : Function.Injective (fun q=> (blockType p q,outerBlocks C l p o q))
  valid : ∀i,(outerBlocks C l p o (label p i)).val∈
    (C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l i)).candidates
  nonbulk_pos : 0 < (selectedNonbulkPrior C l).mass (outerNonbulk C l p o)
  left_mass : ∀i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
    choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l
      (leftChoices C (leftBlockDraws C p ⟨outerBlocks C l p o,typed⟩ valid) i)≠0
  right_mass : ∀i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
    choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l
      (rightChoices C (rightBlockDraws C p ⟨outerBlocks C l p o,typed⟩ valid) i)≠0

namespace OuterData
variable {C p o}
def blockDraw (D : OuterData C p o) :
    BlockDraw p (CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :=
  ⟨outerBlocks C l p o,D.typed⟩
@[simp] theorem blockDraw_value (D : OuterData C p o) (q : Block p) :
    D.blockDraw.val q=outerBlocks C l p o q := rfl
end OuterData

def outerData? : Option (OuterData C p o) := by
  classical
  exact if ht : Function.Injective (fun q=>(blockType p q,outerBlocks C l p o q)) then
    if hv : ∀i,(outerBlocks C l p o (label p i)).val∈
      (C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l i)).candidates then
    if ha : 0 < (selectedNonbulkPrior C l).mass (outerNonbulk C l p o) then
    if hc : ∀i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
      choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l
        (leftChoices C (leftBlockDraws C p ⟨outerBlocks C l p o,ht⟩ hv) i)≠0 then
    if he : ∀i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
      choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l
        (rightChoices C (rightBlockDraws C p ⟨outerBlocks C l p o,ht⟩ hv) i)≠0 then
      some ⟨ht,hv,ha,hc,he⟩ else none else none else none else none else none

theorem outerData?_isSome_iff : (outerData? C p o).isSome ↔ Nonempty (OuterData C p o) := by
  classical
  constructor
  · intro h
    exact ⟨(outerData? C p o).get h⟩
  · rintro ⟨D⟩
    unfold outerData?
    simp only [dite_eq_left D.typed,dite_eq_left D.valid,dite_eq_left D.nonbulk_pos,
      dite_eq_left D.left_mass,dite_eq_left D.right_mass,Option.isSome_some]

end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
