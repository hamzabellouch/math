import OAI.Combinatorics.MatroidCounting.CommonBases

namespace OAI

/-! # Rational medians with real target intervals -/

namespace ContingencyTables.FiniteMedianConfidence

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

/-- Rational thresholds used only in the proof permit direct reuse of
finite median amplification when the intended target is a real number. -/
theorem median_confidence_real {X : Type*} [Fintype X] [Nonempty X]
    (output : X → ℚ) (L L' U' U : ℝ) (hL : L < L') (hU : U' < U)
    (delta : ℚ) (hdelta : 0 < delta)
    (hbad : uniformAverage (fun x =>
      if (output x:ℝ) < L' ∨ U' < (output x:ℝ) then (1:ℝ) else 0) ≤ 5/16) :
    1-(delta:ℝ) ≤ uniformAverage (fun xs : Fin (repetitionCount delta) → X =>
      if L ≤ (rationalMedian (List.ofFn (fun i => output (xs i))):ℝ) ∧
        (rationalMedian (List.ofFn (fun i => output (xs i))):ℝ) ≤ U
      then (1:ℝ) else 0) := by
  obtain ⟨a,haL,haL'⟩ := exists_rat_btwn hL
  obtain ⟨b,hU'b,hbU⟩ := exists_rat_btwn hU
  have hab : uniformAverage (fun x => if outsideInterval a b (output x) then (1:ℝ) else 0) ≤ 5/16 := by
    apply (uniformAverage_mono _ _ (fun x => ?_)).trans hbad
    simp only [outsideInterval,decide_eq_true_eq]
    by_cases hn : ¬(a ≤ output x ∧ output x ≤ b)
    · have hor : output x < a ∨ b < output x := by
        by_cases ha : output x < a
        · exact Or.inl ha
        · right
          by_contra hb
          exact hn ⟨le_of_not_gt ha,le_of_not_gt hb⟩
      have ht : (output x:ℝ) < L' ∨ U' < (output x:ℝ) := by
        rcases hor with ha|hb
        · left
          exact lt_trans (by exact_mod_cast ha) haL'
        · right
          exact lt_trans hU'b (by exact_mod_cast hb)
      simp [hn,ht]
    · simp only [hn,ite_false]
      split_ifs <;> norm_num
  have hm := median_confidence output a b delta hdelta hab
  apply hm.trans
  apply uniformAverage_mono
  intro xs
  by_cases hg : a ≤ rationalMedian (List.ofFn (fun i => output (xs i))) ∧
      rationalMedian (List.ofFn (fun i => output (xs i))) ≤ b
  · have hreal : L ≤ (rationalMedian (List.ofFn (fun i => output (xs i))):ℝ) ∧
        (rationalMedian (List.ofFn (fun i => output (xs i))):ℝ) ≤ U :=
      ⟨le_trans haL.le (by exact_mod_cast hg.1),le_trans (by exact_mod_cast hg.2) hbU.le⟩
    simp [hg,hreal]
  · simp only [hg,ite_false]
    split_ifs <;> norm_num

lemma rationalMedian_mem (l : List ℚ) (hl : 0 < l.length) : rationalMedian l ∈ l := by
  have hi : l.length/2 < (l.mergeSort (· ≤ ·)).length := by
    rw [List.length_mergeSort]
    omega
  unfold rationalMedian
  rw [List.getD_eq_getElem _ _ hi]
  exact List.mem_mergeSort.mp (List.getElem_mem hi)

end

end ContingencyTables.FiniteMedianConfidence

end OAI
