import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyMatchedMetadata
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyMatchedSelection

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryPairBulkTransport HistoryPairPattern
attribute [local instance] Classical.propDecidable
local instance actualPrincipalMatchedSelectedDataInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ}
  {σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))}
  {J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → SelectedBulkSample C l → ℤ → ℤ → ℂ}
  {α : Type} [Fintype α] {w : α→ℝ} {P Q : α→ℤ}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}
namespace MatchedSelectedOuter
variable (R : MatchedSelectedOuter C p o outside σ J w P Q i)

def blockReference : MatchedBlockReference C.sources (Template.initial (2*(bulkSize k L/2)) k)
    (frequencyBound Bs BD Bz k L) outside l p :=
  matchedWitnessBlockReference C p R.data.blockDraw R.data.valid outside σ (outerNonbulk C l p o)
    J w P Q i R.witness

theorem rootAligned (j : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length) :
    coordinateSample _ R.blockReference.right.history R.blockReference.right.labels (.inr (.inl j))=
      coordinateSample _ R.blockReference.left.history R.blockReference.left.labels (.inr (.inl (selectedLeafPermutation C l σ j))) :=
  matchedWitnessBlockReference_rootAligned C p R.data.blockDraw R.data.valid outside σ (outerNonbulk C l p o)
    J w P Q i R.witness j

theorem giants : RootGiantsAgree R.blockReference.left.history R.blockReference.right.history :=
  matchedWitnessBlockReference_giants C p R.data.blockDraw R.data.valid outside σ (outerNonbulk C l p o)
    J w P Q i R.witness

def principalData
    (hcell : ∀v,w v≠0 → 0<P v ∧ 0<Q v ∧
      |Real.log (P v:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q v:ℝ)-(C.giantCenter:ℝ)|≤1)
    (s : ℕ) (hlen : outside.length=2*s) (hprime : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
    (independent : Bool) : MatchedPrincipalReferenceData C R.blockReference :=
  matchedWitnessPrincipalData C p R.data.blockDraw R.data.valid outside σ (outerNonbulk C l p o)
    J w P Q i R.witness R.data.nonbulk_pos (R.data.left_mass i) (R.data.right_mass i)
    hcell s hlen hprime hV independent

end MatchedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
