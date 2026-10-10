import OAI.Analysis.Laughlin.ThreeBody.HighestRow

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem threeBodyGram_highest_first_coordinate (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    (∑ q : Fin (z+1), threeBodyGramSlice Q z hz ⟨0,by omega⟩ q *
      Spin.highestUnit (2*Q-2) Q z q.val) =
      (1+gramEigenvalueFormula Q z)*Spin.highestUnit (2*Q-2) Q z 0 := by
  by_cases hz₀ : z=0
  · subst z
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
    change (1-2*∑ t : Fin (Q+1),
      pairCoefficient Q 0 ⟨0,Nat.zero_lt_succ Q⟩ t *
      pairCoefficient Q 0 ⟨0,Nat.zero_lt_succ Q⟩ t) *
      Spin.highestUnit (2*Q-2) Q 0 0 + 0 = _
    rw [swap_base_row Q 0 hQ]
    simp [pairCoefficient_base Q hQ,gramEigenvalueFormula,fallingRatio]
    left
    have hn : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  · rw [threeBodyGramSlice_first_row_pos Q z hQ hz (by omega)]
    have he := Spin.highestReadout_eq_formula Q z hQ hz
    unfold Spin.highestReadout at he
    rw [ite_eq_right hz₀] at he
    linear_combination he

noncomputable def threeBodyHighest (Q z : ℕ) (hz : z ≤ Q) : Space Q :=
  ∑ p : Fin (z+1), (Spin.highestUnit (2*Q-2) Q z p.val : ℂ) •
    threeBodyColumn Q p.val (sliceOrbital Q z hz p)

theorem threeBodyHighest_first_inner (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    occupationInner Q (threeBodyColumn Q 0 ⟨z,by omega⟩) (threeBodyHighest Q z hz) =
      (((1+gramEigenvalueFormula Q z)*Spin.highestUnit (2*Q-2) Q z 0 : ℝ) : ℂ) := by
  unfold threeBodyHighest
  rw [occupationInner_sum_right]
  simp only [occupationInner_smul_right]
  have hrow := congrArg (fun x : ℝ => (x : ℂ))
    (threeBodyGram_highest_first_coordinate Q z hQ hz)
  push_cast at hrow
  push_cast
  rw [← hrow]
  apply Finset.sum_congr rfl
  intro p hp
  rw [threeBodyGramSlice_physical Q z hQ hz]
  exact mul_comm _ _

end Laughlin.Fock

end OAI
