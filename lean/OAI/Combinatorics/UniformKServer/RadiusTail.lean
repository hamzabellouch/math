import Mathlib

namespace OAI

                                 
section
namespace UniformKServer.RadiusTail
noncomputable section

def clipped (a : ℝ) : ℝ := min (max (a-1) 0) 1

/-- Survival function of the manuscript's truncated exponential radius,
normalized by r. It includes support endpoints with their exact values. -/
def tail (lam a : ℝ) : ℝ :=
  (Real.exp (-lam*clipped a)-Real.exp (-lam))/(1-Real.exp (-lam))
theorem clipped_bounds (a : ℝ) : clipped a ∈ Set.Icc (0:ℝ) 1 := by
  exact ⟨le_min (le_max_right _ _) zero_le_one,min_le_right _ _⟩

theorem clipped_mono : Monotone clipped := by
  intro a b hab
  exact min_le_min (max_le_max (sub_le_sub_right hab 1) le_rfl) le_rfl

theorem clipped_difference (a b : ℝ) (hab : a ≤ b) : clipped b-clipped a ≤ b-a := by
  unfold clipped
  rcases le_total (a-1) 0 with ha|ha
  · rw [max_eq_right ha,min_eq_left zero_le_one]
    rcases le_total (b-1) 0 with hb|hb
    · rw [max_eq_right hb,min_eq_left zero_le_one]
      linarith
    · rw [max_eq_left hb]
      linarith [min_le_left (b-1) (1:ℝ)]
  · rw [max_eq_left ha,max_eq_left (by linarith : 0 ≤ b-1)]
    rcases le_total (a-1) 1 with ha1|ha1
    · rw [min_eq_left ha1]
      linarith [min_le_left (b-1) (1:ℝ)]
    · rw [min_eq_right ha1,min_eq_right (by linarith : 1 ≤ b-1)]
      linarith

theorem denominator_pos (lam : ℝ) (hlam : 0 < lam) : 0 < 1-Real.exp (-lam) := by
  have : Real.exp (-lam) < 1 := (Real.exp_lt_one_iff).mpr (by linarith)
  linarith

theorem tail_bounds (lam a : ℝ) (hlam : 0 < lam) : tail lam a ∈ Set.Icc (0:ℝ) 1 := by
  have hc := clipped_bounds a
  have hlo : Real.exp (-lam) ≤ Real.exp (-lam*clipped a) := Real.exp_le_exp.mpr (by nlinarith [hc.2])
  have hhi : Real.exp (-lam*clipped a) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hc.1])
  unfold tail
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlo) (denominator_pos lam hlam).le
  · apply (div_le_one (denominator_pos lam hlam)).mpr
    linarith

theorem tail_antitone (lam : ℝ) (hlam : 0 < lam) : Antitone (tail lam) := by
  intro a b hab
  unfold tail
  apply div_le_div_of_nonneg_right _ (denominator_pos lam hlam).le
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  have := clipped_mono hab
  nlinarith

theorem tail_eq_one (lam a : ℝ) (hlam : 0 < lam) (ha : a ≤ 1) : tail lam a = 1 := by
  have hc : clipped a = 0 := by
    unfold clipped
    rw [max_eq_right (by linarith),min_eq_left zero_le_one]
  unfold tail
  rw [hc,mul_zero,Real.exp_zero]
  exact div_self (ne_of_gt (denominator_pos lam hlam))

theorem tail_eq_zero (lam a : ℝ) (ha : 2 ≤ a) : tail lam a = 0 := by
  have hc : clipped a = 1 := by
    unfold clipped
    rw [max_eq_left (by linarith),min_eq_right (by linarith)]
  simp only [tail,hc,mul_one,sub_self,zero_div]

theorem tail_offset (lam a : ℝ) (hlam : 0 < lam) :
    tail lam a+1/(Real.exp lam-1) = Real.exp (-lam*clipped a)/(1-Real.exp (-lam)) := by
  have hx : Real.exp lam-1 ≠ 0 := ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hlam))
  have hd := ne_of_gt (denominator_pos lam hlam)
  have he : Real.exp lam ≠ 0 := ne_of_gt (Real.exp_pos lam)
  have hid : Real.exp (-lam)*(Real.exp lam-1) = 1-Real.exp (-lam) := by
    rw [mul_sub,Real.exp_neg,inv_mul_cancel₀ he,mul_one]
  unfold tail
  field_simp
  nlinarith [hid]
/-- Exact separation-tail estimate, including intervals crossing either end
of the support. The two actual distances are later substituted for a,b. -/
theorem tail_difference (lam a b : ℝ) (hlam : 0 < lam) (hab : a ≤ b) :
    tail lam a-tail lam b ≤ lam*(b-a)*(tail lam a+1/(Real.exp lam-1))
 := by
  have hd := denominator_pos lam hlam
  have hca := clipped_bounds a
  have hc := clipped_mono hab
  have heq : Real.exp (-lam*clipped b) =
      Real.exp (-lam*clipped a)*Real.exp (-lam*(clipped b-clipped a)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have hexp : 1-Real.exp (-lam*(clipped b-clipped a)) ≤ lam*(clipped b-clipped a) := by
    have := Real.add_one_le_exp (-lam*(clipped b-clipped a))
    linarith
  have hstep : 1-Real.exp (-lam*(clipped b-clipped a)) ≤ lam*(b-a) :=
    hexp.trans (mul_le_mul_of_nonneg_left (clipped_difference a b hab) hlam.le)
  rw [tail_offset lam a hlam]
  calc
    tail lam a-tail lam b =
        Real.exp (-lam*clipped a)*(1-Real.exp (-lam*(clipped b-clipped a)))/(1-Real.exp (-lam)) := by
      unfold tail
      rw [heq,←sub_div]
      congr 1
      ring
    _ ≤ Real.exp (-lam*clipped a)*(lam*(b-a))/(1-Real.exp (-lam)) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hstep (Real.exp_pos _).le) hd.le
    _ = _ := by ring
end
end UniformKServer.RadiusTail

end



end OAI
