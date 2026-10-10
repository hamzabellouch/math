import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperSmallMixing

namespace OAI

/-! # Uniform size bounds for the state-dependent dense completion call -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma reference_free_dimension (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) :
    Fintype.card ({i : LargeRows r U // i≠i₀} × {j : LargeColumns c U // j≠j₀}) ≤
      dimensionAllowance (I := I) (J := J) := by
  have hr : Fintype.card {i : LargeRows r U // i≠i₀} ≤ Fintype.card I :=
    (Fintype.card_subtype_le _).trans (Fintype.card_subtype_le _)
  have hc : Fintype.card {j : LargeColumns c U // j≠j₀} ≤ Fintype.card J :=
    (Fintype.card_subtype_le _).trans (Fintype.card_subtype_le _)
  rw [Fintype.card_prod]
  exact (Nat.mul_le_mul hr hc).trans dimension_le_allowance

omit [LinearOrder I] [LinearOrder J] in
lemma reference_dimension_fourteen (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) :
    14 ≤ dimensionAllowance (I := I) (J := J) := by
  have hr : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i₀.val⟩
  have hc : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨j₀.val⟩
  unfold dimensionAllowance
  nlinarith

lemma reference_row_le_stateBound (r : I → ℕ) (c : J → ℕ)
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (z : PaperStates r c) (i : Option {i : LargeRows r ((dimensionAllowance (I := I) (J := J))^20) // i≠i₀}) :
    referenceRows r c _ _ (stateCapacity r c) i₀ z i ≤ stateBound r c := by
  let k := ((Equiv.optionSubtypeNe i₀) i).val
  have hr : r k ≤ ∑ a,r a := Finset.single_le_sum (f := r) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have hcount : rowLargeCount (paperSmall r c) k ≤ Fintype.card J := by
    unfold rowLargeCount
    calc
      _ ≤ ∑ _j : J,(1:ℕ) := Finset.sum_le_sum (fun j _ => by split_ifs <;> omega)
      _ = _ := by simp
  have hdim : Fintype.card J ≤ dimensionAllowance (I := I) (J := J) := by
    unfold dimensionAllowance
    nlinarith
  have hm := Nat.mul_le_mul_right ((dimensionAllowance (I := I) (J := J))^12) (hcount.trans hdim)
  have hs := Nat.sub_le (r k)
    (smallRow (paperSmall r c) (FirstPaperProfiles.smallView (paperSmall r c)
      (physicalProfile _ (stateCapacity r c) r c _ z) false) k)
  unfold referenceRows residualRows stateBound
  change r k-_+rowLargeCount (paperSmall r c) k*((dimensionAllowance (I := I) (J := J))^12) ≤ _
  omega

end ContingencyTables.SmallGraphProfiles

end OAI
