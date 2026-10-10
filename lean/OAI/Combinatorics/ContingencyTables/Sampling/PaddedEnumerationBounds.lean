import OAI.Combinatorics.ContingencyTables.Rooted.LargeMarginProgram
import OAI.Combinatorics.ContingencyTables.Machines.CompletionEnumerationProgram

namespace OAI

/-! # Enumeration bounds uniform over all proposed small profiles -/

namespace ContingencyTables.ProfilePrograms
open DensePrograms

lemma list_getD_le_sum (as : List ℕ) (i : ℕ) : as.getD i 0 ≤ as.sum := by
  induction as generalizing i with
  | nil => simp
  | cons a as ih =>
    cases i with
    | zero => simp
    | succ i =>
      simpa only [List.getD_cons_succ,List.sum_cons] using
        (ih i).trans (Nat.le_add_left as.sum a)

lemma list_sum_le_length_mul (as : List ℕ) (B : ℕ) (h : ∀ a∈as,a ≤ B) :
    as.sum ≤ as.length*B := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have ha := h a (by simp)
    have hs := ih (by intro b hb; exact h b (by simp [hb]))
    simp only [List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

lemma largeCount_le_length (U : ℕ) (as : List ℕ) : largeCount (U,as) ≤ as.length := by
  unfold largeCount
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    change (as.map (fun a => if U ≤ a then 1 else 0)).sum ≤ as.length at ih
    change (if U ≤ a then 1 else 0)+(as.map (fun a => if U ≤ a then 1 else 0)).sum ≤ as.length+1
    split_ifs <;> omega

/-- Rejected profiles can decrease residual margins but cannot enlarge
them beyond the original margin and its deterministic padding. -/
lemma paddedMarginAt_le (row : Bool) (z : PaddingData) (i : ℕ) :
    paddedMarginAt row (z,i) ≤
      (marginList row z.1).sum+(marginList (!row) z.1).length*z.2 := by
  have ha := list_getD_le_sum (marginList row z.1) i
  have hc := largeCount_le_length z.1.2 (marginList (!row) z.1)
  have hs : (marginList row z.1).getD i 0-lineSum row (lineArgument row (z.1,i)) ≤
      (marginList row z.1).sum := (Nat.sub_le _ _).trans ha
  unfold paddedMarginAt largeFlag
  dsimp only
  split_ifs
  · simpa only [one_mul] using Nat.add_le_add hs (Nat.mul_le_mul_right z.2 hc)
  · simpa only [zero_mul,add_zero] using hs.trans (Nat.le_add_right _ _)

lemma largePaddedMargins_length (row : Bool) (z : PaddingData) :
    (largePaddedMargins row z).length ≤ (marginList row z.1).length := by
  rw [largePaddedMargins_eq,List.length_map]
  exact (List.length_filter_le _ _).trans_eq List.length_range

lemma largePaddedMargins_entry (row : Bool) (z : PaddingData) (a : ℕ)
    (ha : a∈largePaddedMargins row z) :
    a ≤ (marginList row z.1).sum+(marginList (!row) z.1).length*z.2 := by
  rw [largePaddedMargins_eq] at ha
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  exact paddedMarginAt_le row z i

lemma largePaddedMargins_sum (row : Bool) (z : PaddingData) :
    (largePaddedMargins row z).sum ≤ (marginList row z.1).length*
      ((marginList row z.1).sum+(marginList (!row) z.1).length*z.2) := by
  exact (list_sum_le_length_mul _ _ (largePaddedMargins_entry row z)).trans
    (Nat.mul_le_mul_right _ (largePaddedMargins_length row z))

end ContingencyTables.ProfilePrograms

end OAI
