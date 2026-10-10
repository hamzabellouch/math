import OAI.Geometry.RCD.Sobolev.TransverseTestFormula

namespace OAI

/-! # The transverse barrier error depends only on its two Gram entries -/

namespace RegularPointCoordinates

theorem transverse_test_error (W S δ c g h : ℝ) :
    |((if -δ<W then max (c-S) 0*g else 0)-
        (if S<c then max (W+δ) 0*h else 0))-
      (if -δ<W then max (c-S) 0 else 0)| ≤
      max (c-S) 0*|g-1|+max (W+δ) 0*|h| := by
  have hA : 0≤ max (c-S) 0 := le_max_right _ _
  have hB : 0≤ max (W+δ) 0 := le_max_right _ _
  by_cases hW : -δ<W
  · by_cases hS : S<c
    · simp only [hW,hS,ite_true]
      calc
        _=|max (c-S) 0*(g-1)-max (W+δ) 0*h| := by congr 1; ring
        _≤|max (c-S) 0*(g-1)|+|max (W+δ) 0*h| := abs_sub _ _
        _=_ := by rw [abs_mul,abs_mul,abs_of_nonneg hA,abs_of_nonneg hB]
    · simp only [hW,hS,ite_true,ite_false,sub_zero]
      have hh : |max (c-S) 0*g-max (c-S) 0|=max (c-S) 0*|g-1| := by
        calc
          _=|max (c-S) 0*(g-1)| := by congr 1; ring
          _=_ := by rw [abs_mul,abs_of_nonneg hA]
      rw [hh]
      linarith [mul_nonneg hB (abs_nonneg h)]
  · by_cases hS : S<c
    · simp only [hW,hS,ite_true,ite_false,zero_sub,sub_zero,abs_neg,abs_mul,abs_of_nonneg hB]
      linarith [mul_nonneg hA (abs_nonneg (g-1))]
    · simp only [hW,hS,ite_false,sub_zero,abs_zero]
      positivity

theorem transverse_test_error_of_bounds {W S δ c g h M : ℝ}
    (hc : 0≤c) (hS : 0≤S) (hW : |W|≤M) :
    |((if -δ<W then max (c-S) 0*g else 0)-
        (if S<c then max (W+δ) 0*h else 0))-
      (if -δ<W then max (c-S) 0 else 0)| ≤
      c*|g-1|+(M+|δ|)*|h| := by
  apply (transverse_test_error W S δ c g h).trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (max_le (by linarith) hc) (abs_nonneg _)
  · apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    have hM : 0≤M := (abs_nonneg _).trans hW
    exact max_le (by linarith [le_abs_self W,le_abs_self δ]) (by positivity)

end RegularPointCoordinates

end OAI
