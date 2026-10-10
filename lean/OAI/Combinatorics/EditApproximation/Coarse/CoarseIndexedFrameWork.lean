import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedRead
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalGridWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

/-- Read the framed target from its original array and three integer indices. -/


theorem coarseFramedReadWithWork_value {α : Type*} (k n : ℕ) (word : List α) (i : ℕ) :
    (coarseFramedReadWithWork k n word i).1 = coarseFramedRead k n word i := by
  unfold coarseFramedReadWithWork coarseFramedRead
  dsimp only
  by_cases hlo : i < k
  · rw [ite_eq_left ((binaryNaturalCompareWithWork_lt i k).mpr hlo), ite_eq_right (by omega)]
  · rw [ite_eq_right (fun h => hlo ((binaryNaturalCompareWithWork_lt i k).mp h))]
    simp only [binaryNaturalAddWithWork_value]
    by_cases hhi : i < k + n
    · rw [ite_eq_left ((binaryNaturalCompareWithWork_lt i (k + n)).mpr hhi),
        ite_eq_left (by omega)]
      simp only [saturatingSubtractWithWork_value]
    · rw [ite_eq_right (fun h => hhi ((binaryNaturalCompareWithWork_lt i (k + n)).mp h)),
        ite_eq_right (by omega)]

theorem coarseFramedReadWithWork_cost {α : Type*} (k n : ℕ) (word : List α) (i A : ℕ)
    (hk : Nat.size k ≤ A) (hn : Nat.size n ≤ A) (hi : Nat.size i ≤ A) :
    (coarseFramedReadWithWork k n word i).2 ≤ 100 * (A + 1) := by
  have hl := binaryNaturalCompareWithWork_cost i k
  have ha := binaryNaturalAddWithWork_cost k n
  have hs := binaryNaturalAdd_size_le k n
  have hmax : max (Nat.size k) (Nat.size n) ≤ A := max_le hk hn
  have hu := binaryNaturalCompareWithWork_cost i (bitWordValue (binaryNaturalAddWithWork k n).1)
  rw [binaryNaturalAddWithWork_value] at hu
  have hd := saturatingSubtractWithWork_cost i k
  unfold coarseFramedReadWithWork
  dsimp only
  simp only [binaryNaturalAddWithWork_value]
  split_ifs <;> dsimp only <;> omega

theorem coarseIndexed_leaf_cost {α : Type*} [DecidableEq α] {B : ℕ}
    (k n : ℕ) (word : List α) (hn : word.length ≤ n) (letter : Option α)
    (start : ℕ) (shift : Fin (2 * k + 1)) :
    coarseShiftCost k (coarseTargetFrame k (coarsePadTo n word))
      (.leaf (B := B) (some letter)) start shift =
      if (coarseFramedReadWithWork k n word (start + shift.val)).1 = some letter then 0 else 1 := by
  rw [coarseFramedReadWithWork_value, coarseFramedRead_value k n word hn]
  rfl

end EditApproximation

end OAI
