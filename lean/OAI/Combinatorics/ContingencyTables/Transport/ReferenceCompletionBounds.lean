import OAI.Combinatorics.ContingencyTables.Transport.ReferenceCompletionBlock

namespace OAI

/-! # Padding and dimension bounds for the actual reference completion block -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma large_row_padding (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (i : LargeRows r U) (j : LargeColumns c U) :
    L ≤ residualRows (firstPaperSmall r c U) B r c L z i.val := by
  have hs := (firstPaperSmall_false_iff r c U i.val j.val).mpr ⟨i.property,j.property⟩
  have hh := Finset.single_le_sum
    (f := fun j' => if firstPaperSmall r c U i.val j' then 0 else 1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j.val)
  have hc : 1 ≤ rowLargeCount (firstPaperSmall r c U) i.val := by
    simpa only [rowLargeCount,hs,Bool.false_eq_true,ite_false] using hh
  unfold residualRows
  nlinarith

lemma large_column_padding (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (i : LargeRows r U) (j : LargeColumns c U) :
    L ≤ residualColumns (firstPaperSmall r c U) B r c L z j.val := by
  have hs := (firstPaperSmall_false_iff r c U i.val j.val).mpr ⟨i.property,j.property⟩
  have hh := Finset.single_le_sum
    (f := fun i' => if firstPaperSmall r c U i' j.val then 0 else 1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i.val)
  have hc : 1 ≤ columnLargeCount (firstPaperSmall r c U) j.val := by
    simpa only [columnLargeCount,hs,Bool.false_eq_true,ite_false] using hh
  unfold residualColumns
  nlinarith

lemma reference_row_padding (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (i : Option {i : LargeRows r U // i≠i₀}) : L ≤ referenceRows r c U L B i₀ z i :=
  large_row_padding r c U L B z ((Equiv.optionSubtypeNe i₀) i) j₀

lemma reference_column_padding (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (j : Option {j : LargeColumns c U // j≠j₀}) : L ≤ referenceColumns r c U L B j₀ z j :=
  large_column_padding r c U L B z i₀ ((Equiv.optionSubtypeNe j₀) j)

lemma reference_block_dimensions (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) :
    Fintype.card (Option {i : LargeRows r U // i≠i₀}) ≤ dimensionAllowance (I := I) (J := J) ∧
    Fintype.card (Option {j : LargeColumns c U // j≠j₀}) ≤ dimensionAllowance (I := I) (J := J) ∧
    Fintype.card {i : LargeRows r U // i≠i₀}+Fintype.card {j : LargeColumns c U // j≠j₀}+1 ≤
      dimensionAllowance (I := I) (J := J) := by
  have hri := Fintype.card_congr (Equiv.optionSubtypeNe i₀)
  have hcj := Fintype.card_congr (Equiv.optionSubtypeNe j₀)
  have hr : Fintype.card (LargeRows r U) ≤ Fintype.card I := Fintype.card_subtype_le _
  have hc : Fintype.card (LargeColumns c U) ≤ Fintype.card J := Fintype.card_subtype_le _
  rw [Fintype.card_option] at hri hcj
  simp only [Fintype.card_option]
  unfold dimensionAllowance
  constructor
  · nlinarith
  constructor <;> nlinarith

end ContingencyTables.SmallGraphProfiles

end OAI
