import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.TerminalRates
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Geometry

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section
namespace MatrixMultiplication.AllFieldZeroWords
open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldTerminalStatisticLaws AllFieldTerminalRates CWWindowedLeaves
open CWCompleteStatistics InheritedMasks
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K : ℕ}

def length (h : TerminalZero K) : ℕ := currentLength (history h).1
def shape (h : TerminalZero K) : Shape := currentShape (history h).1

def statistic : (h : TerminalZero K) → Raw (length h) → Slot h
  | .inl _, w => fourStatistic w
  | .inr _, w => twoStatistic w

def complement : (h : TerminalZero K) → Slot h ≃ Slot h
  | .inl _ => orderedComplementStatistic
  | .inr _ => complementStatistic

theorem statistic_complement (h : TerminalZero K) (w : Raw (length h)) :
    statistic h (complementWord w) = complement h (statistic h w) := by
  cases h with
  | inl h => exact four_complement w
  | inr h => exact two_complement w

def words (allocation : Allocation) (m : ℕ) (h : TerminalZero K)
    (w : ZeroWords allocation m h) :
    Fin (population allocation (terminalDilation K m) (history h)) →
      Alphabet (length h) (shapeMax (shape h)) := by
  cases h with
  | inl h =>
      exact fun i => w.val ((finCongr (statisticCounts_repeat_sum allocation m (.inl h))).symm i)
  | inr h =>
      exact fun i => w.val ((finCongr (statisticCounts_repeat_sum allocation m (.inr h))).symm i)

theorem words_injective (allocation : Allocation) (m : ℕ) (h : TerminalZero K) :
    Function.Injective (words allocation m h) := by
  cases h with
  | inl h =>
      intro x y he
      apply Subtype.ext
      funext i
      have hh := congrFun he ((finCongr (statisticCounts_repeat_sum allocation m (.inl h))) i)
      change x.val ((finCongr (statisticCounts_repeat_sum allocation m (.inl h))).symm
        ((finCongr (statisticCounts_repeat_sum allocation m (.inl h))) i)) =
        y.val ((finCongr (statisticCounts_repeat_sum allocation m (.inl h))).symm
          ((finCongr (statisticCounts_repeat_sum allocation m (.inl h))) i)) at hh
      exact (congrArg x.val
        ((finCongr (statisticCounts_repeat_sum allocation m (.inl h))).symm_apply_apply i)).symm.trans
          (hh.trans (congrArg y.val
            ((finCongr (statisticCounts_repeat_sum allocation m (.inl h))).symm_apply_apply i)))
  | inr h =>
      intro x y he
      apply Subtype.ext
      funext i
      have hh := congrFun he ((finCongr (statisticCounts_repeat_sum allocation m (.inr h))) i)
      change x.val ((finCongr (statisticCounts_repeat_sum allocation m (.inr h))).symm
        ((finCongr (statisticCounts_repeat_sum allocation m (.inr h))) i)) =
        y.val ((finCongr (statisticCounts_repeat_sum allocation m (.inr h))).symm
          ((finCongr (statisticCounts_repeat_sum allocation m (.inr h))) i)) at hh
      exact (congrArg x.val
        ((finCongr (statisticCounts_repeat_sum allocation m (.inr h))).symm_apply_apply i)).symm.trans
          (hh.trans (congrArg y.val
            ((finCongr (statisticCounts_repeat_sum allocation m (.inr h))).symm_apply_apply i)))

theorem repeat_ratio (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    (h : TerminalZero K) (s : Slot h) :
    ((m * statisticCounts allocation h s : ℕ) : ℝ) /
      (∑ s, m * statisticCounts allocation h s : ℕ) = (law h s : ℝ) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  simp only [← Finset.mul_sum, Nat.cast_mul, mul_div_mul_left _ _ hm']
  exact statisticCounts_ratio allocation h s

theorem selected_window (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    (h : TerminalZero K) (η : ℝ) (hη : 0 ≤ η) (w : ZeroWords allocation m h) :
    typeWindow (fun s => (law h s : ℝ)) η
      (fun i => statistic h (words allocation m h w i).val) := by
  intro s
  have hp : wordPopulation (fun i => statistic h (words allocation m h w i).val) s =
      m * statisticCounts allocation h s := by
    cases h with
    | inl h =>
        calc
          _ = wordPopulation (fun i => fourStatistic (w.val i).val) s := by
            simp only [wordPopulation, Fintype.card_eq_nat_card]
            apply Nat.card_congr
            exact (Equiv.subtypeEquiv
                (finCongr (statisticCounts_repeat_sum allocation m (.inl h))).symm
                (fun _ => Iff.rfl))
          _ = _ := w.property s
    | inr h =>
        calc
          _ = wordPopulation (fun i => twoStatistic (w.val i).val) s := by
            simp only [wordPopulation, Fintype.card_eq_nat_card]
            apply Nat.card_congr
            exact (Equiv.subtypeEquiv
                (finCongr (statisticCounts_repeat_sum allocation m (.inr h))).symm
                (fun _ => Iff.rfl))
          _ = _ := w.property s
  change |(wordPopulation (fun i => statistic h (words allocation m h w i).val) s : ℝ) /
    (Fintype.card (Fin (population allocation (terminalDilation K m) (history h))) : ℝ) -
    (law h s : ℝ)| ≤ η
  rw [hp, Fintype.card_fin, ← statisticCounts_repeat_sum allocation m h,
    repeat_ratio allocation hm h s, sub_self, abs_zero]
  exact hη

theorem complementary_window (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    (h : TerminalZero K) (η : ℝ) (hη : 0 ≤ η) (w : ZeroWords allocation m h) :
    typeWindow ((fun s => (law h s : ℝ)) ∘ (complement h).symm) η
      (fun i => statistic h (complementWord (words allocation m h w i).val)) := by
  have hs := selected_window allocation hm h η hη w
  have he : (fun i => statistic h (complementWord (words allocation m h w i).val)) =
      complement h ∘ (fun i => statistic h (words allocation m h w i).val) := by
    funext i
    exact statistic_complement h _
  rw [he]
  exact (typeWindow_equiv _ η _ (complement h)).mpr hs

end MatrixMultiplication.AllFieldZeroWords

end

end OAI
