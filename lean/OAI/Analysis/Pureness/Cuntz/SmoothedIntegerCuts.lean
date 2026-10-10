import OAI.Analysis.Pureness.Cuntz.IntegerCuts

namespace OAI
namespace CuntzPureness

noncomputable def smoothedIntegerCutCount (l : ℕ) (p t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range l, min (p * max (t - ((j : ℝ) + 1)) 0) 1

lemma smoothedIntegerCutCount_nonneg (l : ℕ) (p t : ℝ) (hp : 0 ≤ p) :
    0 ≤ smoothedIntegerCutCount l p t :=
  Finset.sum_nonneg (fun _ _ => le_min (mul_nonneg hp (le_max_right _ _)) zero_le_one)

theorem smoothedIntegerCutCount_bounds (l : ℕ) (p t : ℝ)
    (hp : 0 < p) (ht : 0 ≤ t) (hl : t ≤ l) :
    0 ≤ t - smoothedIntegerCutCount l p t ∧
      t - smoothedIntegerCutCount l p t ≤ min (p * t) 1 + 1 / p := by
  have hcount : smoothedIntegerCutCount l p t ≤ integerCutCount l t := by
    apply Finset.sum_le_sum
    intro j hj
    by_cases hjt : (j : ℝ) + 1 < t
    · rw [ite_eq_left hjt]
      exact min_le_right _ _
    · rw [ite_eq_right hjt, max_eq_right (by linarith : t - ((j : ℝ) + 1) ≤ 0), mul_zero]
      norm_num
  refine ⟨by linarith [(integerCutCount_bounds l t ht hl).1], ?_⟩
  by_cases hsmall : t ≤ 1 / p
  · have hn := smoothedIntegerCutCount_nonneg l p t hp.le
    have hmin : 0 ≤ min (p * t) 1 := le_min (mul_nonneg hp.le ht) zero_le_one
    linarith
  · have htp : 1 / p < t := lt_of_not_ge hsmall
    have hpt : 1 ≤ p * t := by
      have := (div_lt_iff₀ hp).mp htp
      nlinarith
    rw [min_eq_right hpt]
    have hu0 : 0 ≤ t - 1 / p := by linarith
    have hul : t - 1 / p ≤ l := by linarith [one_div_pos.mpr hp]
    have hpos : 0 < t - 1 / p := by linarith
    have hshift : integerCutCount l (t - 1 / p) ≤ smoothedIntegerCutCount l p t := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hjt : (j : ℝ) + 1 < t - 1 / p
      · rw [ite_eq_left hjt, max_eq_left (by linarith [one_div_pos.mpr hp] : 0 ≤ t - ((j : ℝ) + 1))]
        have hdiff : 1 / p < t - ((j : ℝ) + 1) := by linarith
        have hmul : 1 ≤ p * (t - ((j : ℝ) + 1)) := by
          have := (div_lt_iff₀ hp).mp hdiff
          nlinarith
        rw [min_eq_right hmul]
      · rw [ite_eq_right hjt]
        exact le_min (mul_nonneg hp.le (le_max_right _ _)) zero_le_one
    have hb := (integerCutCount_bounds l (t - 1 / p) hu0 hul).2
    rw [ite_eq_left hpos] at hb
    linarith
end CuntzPureness

end OAI
