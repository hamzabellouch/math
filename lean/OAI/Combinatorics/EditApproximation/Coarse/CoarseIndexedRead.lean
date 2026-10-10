import OAI.Combinatorics.EditApproximation.Coarse.CoarseInitialBinary

namespace OAI

namespace EditApproximation

/-- Padding and framing are index calculations over the original stored
input. These views do not allocate a padded string. -/
def coarsePaddedRead {α : Type*} (n : ℕ) (word : List α) (i : ℕ) : Option (Option α) :=
  if i < n then some word[i]? else none

def coarseFramedRead {α : Type*} (k n : ℕ) (word : List α) (i : ℕ) : Option (Option α) :=
  if k ≤ i ∧ i < k + n then some word[i - k]? else none

theorem coarsePaddedRead_value {α : Type*} (n : ℕ) (word : List α) (hn : word.length ≤ n) (i : ℕ) :
    coarsePaddedRead n word i = (coarsePadTo n word)[i]? := by
  unfold coarsePaddedRead coarsePadTo
  by_cases hi : i < word.length
  · rw [ite_eq_left (hi.trans_le hn), List.getElem?_append_left (by simpa using hi),
      List.getElem?_map, List.getElem?_eq_getElem hi]
    rfl
  · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt hi), List.length_map,
      List.getElem?_replicate, List.getElem?_eq_none (Nat.le_of_not_gt hi)]
    by_cases hin : i < n
    · rw [ite_eq_left hin, ite_eq_left (by omega)]
    · rw [ite_eq_right hin, ite_eq_right (by omega)]

theorem coarseFramedRead_value {α : Type*} (k n : ℕ) (word : List α) (hn : word.length ≤ n) (i : ℕ) :
    coarseFramedRead k n word i =
      (coarseTargetFrame k (coarsePadTo n word))[i]?.getD none := by
  have hl : (List.replicate k (none : Option (Option α)) ++
      (coarsePadTo n word).map some).length = k + n := by
    simp only [List.length_append, List.length_replicate, List.length_map, coarsePadTo_length n word hn]
  unfold coarseFramedRead coarseTargetFrame
  by_cases hi : i < k + n
  · rw [List.getElem?_append_left (by simpa only [hl] using hi)]
    by_cases hk : i < k
    · rw [List.getElem?_append_left (by simpa only [List.length_replicate] using hk),
        List.getElem?_replicate_of_lt hk, Option.getD_some, ite_eq_right (by omega)]
    · rw [List.getElem?_append_right (by simpa only [List.length_replicate] using Nat.le_of_not_gt hk),
        List.length_replicate, List.getElem?_map, ← coarsePaddedRead_value n word hn (i - k)]
      simp only [coarsePaddedRead, ite_eq_left (by omega : i - k < n), Option.map_some,
        Option.getD_some, ite_eq_left (by omega : k ≤ i ∧ i < k + n)]
  · rw [List.getElem?_append_right (by simpa only [hl] using Nat.le_of_not_gt hi), hl,
      List.getElem?_replicate, ite_eq_right (by omega : ¬ (k ≤ i ∧ i < k + n))]
    split_ifs <;> rfl

end EditApproximation

end OAI
