import OAI.Combinatorics.EditApproximation.Geometry.OccurrenceIndex
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Constant-size leaf descriptors use the preprocessed occurrence index.
The target interval is represented by endpoints; it is never copied or
scanned while evaluating a singleton leaf. -/

namespace EditApproximation

def indexedSingletonCost (table : BinaryMemo PositionCounts)
    (symbolBits positionBits a lo hi : ℕ) : ℕ :=
  if lo = hi then 1 else hi - lo -
    if occurrenceQuery table symbolBits positionBits a lo hi = true then 1 else 0

theorem indexedSingletonCost_eq (symbolBits positionBits : ℕ) (target : List ℕ)
    (hsymbol : ∀ a ∈ target, a < 2 ^ symbolBits) (hposition : target.length ≤ 2 ^ positionBits)
    (a lo hi : ℕ) (ha : a < 2 ^ symbolBits) (hlo : lo ≤ hi) (hhi : hi ≤ target.length) :
    indexedSingletonCost (occurrenceBuild symbolBits positionBits target.zipIdx)
      symbolBits positionBits a lo hi = singletonCost a (substring target lo hi) := by
  have hlength := substring_length target lo hi hhi
  have hzero : substring target lo hi = [] ↔ lo = hi := by
    rw [← List.length_eq_zero_iff, hlength]
    omega
  have hocc := occurrenceQuery_target symbolBits positionBits target hsymbol hposition a lo hi ha hlo hhi
  simp only [indexedSingletonCost, singletonCost, hzero, occurrenceDeficit, hlength, hocc]



theorem indexedSingletonCostWithWork_spec (table : BinaryMemo PositionCounts)
    (symbolBits positionBits a lo hi : ℕ) :
    (indexedSingletonCostWithWork table symbolBits positionBits a lo hi).1 =
        indexedSingletonCost table symbolBits positionBits a lo hi ∧
      (indexedSingletonCostWithWork table symbolBits positionBits a lo hi).2 ≤
        2 * symbolBits + 4 * positionBits + 9 := by
  by_cases h : lo = hi
  · simp only [indexedSingletonCostWithWork, indexedSingletonCost, h, ite_true]
    exact ⟨True.intro, by omega⟩
  · simp only [indexedSingletonCostWithWork, indexedSingletonCost, h, ite_false]
    rw [occurrenceQueryWithWork_spec]
    exact ⟨rfl, by omega⟩

def indexedLeafCost (table : BinaryMemo PositionCounts)
    (symbolBits positionBits : ℕ) (symbol : Option ℕ) (lo hi : ℕ) : ℕ :=
  match symbol with
  | none => hi - lo
  | some a => indexedSingletonCost table symbolBits positionBits a lo hi

theorem indexedLeafCost_eq (symbolBits positionBits : ℕ) (source target : List ℕ)
    (hsource : ∀ a ∈ source, a < 2 ^ symbolBits)
    (htarget : ∀ a ∈ target, a < 2 ^ symbolBits) (hposition : target.length ≤ 2 ^ positionBits)
    (lo hi : ℕ) (hlo : lo ≤ hi) (hhi : hi ≤ target.length) :
    indexedLeafCost (occurrenceBuild symbolBits positionBits target.zipIdx)
      symbolBits positionBits source.head? lo hi = shortSourceCost source (substring target lo hi) := by
  cases source with
  | nil => exact (substring_length target lo hi hhi).symm
  | cons a rest =>
    exact indexedSingletonCost_eq symbolBits positionBits target htarget hposition a lo hi
      (hsource a (by simp only [List.mem_cons, true_or])) hlo hhi

theorem indexedLeafCost_exact (symbolBits positionBits : ℕ) (source target : List ℕ)
    (hsource : ∀ a ∈ source, a < 2 ^ symbolBits)
    (htarget : ∀ a ∈ target, a < 2 ^ symbolBits) (hposition : target.length ≤ 2 ^ positionBits)
    (lo hi : ℕ) (hlo : lo ≤ hi) (hhi : hi ≤ target.length) (hleaf : source.length ≤ 1) :
    indexedLeafCost (occurrenceBuild symbolBits positionBits target.zipIdx)
      symbolBits positionBits source.head? lo hi = EditDistortion.edit source (substring target lo hi) := by
  rw [indexedLeafCost_eq symbolBits positionBits source target hsource htarget hposition lo hi hlo hhi]
  exact shortSourceCost_eq_edit source _ hleaf

end EditApproximation

end OAI
