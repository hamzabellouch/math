import OAI.NumberTheory.CubicMoment.Estimates.PolynomialMeanValue

namespace OAI

/-! Logarithmic frequency separation for the Dirichlet mean value bound. -/
noncomputable section
namespace CubicFirstMoment

lemma log_frequency_spacing {R x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxR : x ≤ R) (hyR : y ≤ R) :
    |x-y| ≤ R*|Real.log x-Real.log y| := by
  have hordered {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
      (hxy : y ≤ x) (hxR : x ≤ R) :
      x-y ≤ R*(Real.log x-Real.log y) := by
    have hlog : Real.log y-Real.log x ≤ y/x-1 := by
      rw [← Real.log_div hy.ne' hx.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hy hx)
    have hm := mul_le_mul_of_nonneg_left hlog hx.le
    have he : x*(y/x-1) = y-x := by field_simp
    rw [he] at hm
    have hl : 0 ≤ Real.log x-Real.log y :=
      sub_nonneg.mpr (Real.log_le_log hy hxy)
    apply le_trans (b := x*(Real.log x-Real.log y))
    · nlinarith
    · exact mul_le_mul_of_nonneg_right hxR hl
  by_cases hxy : y ≤ x
  · rw [abs_of_nonneg (sub_nonneg.mpr hxy),
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy hxy))]
    exact hordered hx hy hxy hxR
  · have hyx := le_of_not_ge hxy
    rw [abs_sub_comm x y,abs_sub_comm (Real.log x) (Real.log y),
      abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hx hyx))]
    exact hordered hy hx hyx hyR

lemma integer_log_frequency_spacing {Z m n : ℕ} (hm : m ∈ Finset.Icc 1 Z)
    (hn : n ∈ Finset.Icc 1 Z) :
    |(m:ℝ)-(n:ℝ)| ≤ (Z:ℝ)*|Real.log (m:ℝ)-Real.log (n:ℝ)| := by
  obtain ⟨hm1,hmZ⟩ := Finset.mem_Icc.mp hm
  obtain ⟨hn1,hnZ⟩ := Finset.mem_Icc.mp hn
  exact log_frequency_spacing (by exact_mod_cast (zero_lt_one.trans_le hm1))
    (by exact_mod_cast (zero_lt_one.trans_le hn1))
    (by exact_mod_cast hmZ) (by exact_mod_cast hnZ)

end CubicFirstMoment

end

end OAI
