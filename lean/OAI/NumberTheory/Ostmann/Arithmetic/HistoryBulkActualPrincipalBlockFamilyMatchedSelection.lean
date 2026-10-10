import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterData
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamilySelection

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration
attribute [local instance] Classical.propDecidable
local instance actualPrincipalMatchedSelectionInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
  (outside : List ℕ) (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {α : Type} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
  (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))

structure MatchedSelectedOuter where
  data : OuterData C p o
  witness : Witness C outside σ (outerNonbulk C l p o)
    (leftBlockDraws C p data.blockDraw data.valid) (rightBlockDraws C p data.blockDraw data.valid)
    J w P Q i

variable {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (houtside : ∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q)
  (hw : ∀r,0≤w r) (hpos : ∀r,w r≠0 → 0<P r ∧ 0<Q r)

def selectMatchedOuterReference : Option (MatchedSelectedOuter C p o outside σ J w P Q i) :=
  match outerData? C p o with
  | none => none
  | some D => (selectWitness C outside σ (outerNonbulk C l p o)
      (leftBlockDraws C p D.blockDraw D.valid) (rightBlockDraws C p D.blockDraw D.valid)
      J w P Q hactual hl D.nonbulk_pos D.left_mass D.right_mass houtside hw hpos i).map
        (fun r=>⟨D,r⟩)

theorem selectMatchedOuterReference_eq_map (D : OuterData C p o) (hD : outerData? C p o=some D) :
    selectMatchedOuterReference C p o outside σ J w P Q i hactual hl houtside hw hpos=
      (selectWitness C outside σ (outerNonbulk C l p o)
        (leftBlockDraws C p D.blockDraw D.valid) (rightBlockDraws C p D.blockDraw D.valid)
        J w P Q hactual hl D.nonbulk_pos D.left_mass D.right_mass houtside hw hpos i).map
          (fun r=>⟨D,r⟩) := by
  unfold selectMatchedOuterReference
  rw [hD]

theorem selectMatchedOuterReference_none_iff (D : OuterData C p o) (hD : outerData? C p o=some D) :
    selectMatchedOuterReference C p o outside σ J w P Q i hactual hl houtside hw hpos=none ↔
      wholeMean C outside σ (outerNonbulk C l p o)
        (leftBlockDraws C p D.blockDraw D.valid) (rightBlockDraws C p D.blockDraw D.valid) J w P Q i=0 := by
  rw [selectMatchedOuterReference_eq_map C p o outside σ J w P Q i hactual hl houtside hw hpos D hD,
    Option.map_eq_none_iff]
  exact selectWitness_none_iff C outside σ (outerNonbulk C l p o)
    (leftBlockDraws C p D.blockDraw D.valid) (rightBlockDraws C p D.blockDraw D.valid)
    J w P Q hactual hl D.nonbulk_pos D.left_mass D.right_mass houtside hw hpos i

end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
