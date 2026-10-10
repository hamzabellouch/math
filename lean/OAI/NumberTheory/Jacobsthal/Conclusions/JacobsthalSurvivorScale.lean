import OAI.NumberTheory.Jacobsthal.Conclusions.JacobsthalSourceRounding

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.JacobsthalSurvivorScale

theorem normalized_scale_lower {x l L w V0 Y c0 : ℝ}
    (hx : 0 < x) (hl : 0 < l) (hlL : l ≤ L) (hLl : L ≤ 2*l)
    (hw : 1 < w) (hc0 : 0 < c0) (hY : x^2/8 ≤ Y) (hV : c0/Real.log w ≤ V0) :
    c0*x^2*Real.log w/(32*l^2) ≤ Y*V0/(L/Real.log w)^2 := by
  have hL : 0 < L := hl.trans_le hlL
  have hlog : 0 < Real.log w := Real.log_pos hw
  have hY0 : 0 ≤ Y := (div_pos (sq_pos_of_pos hx) (by norm_num : (0:ℝ)<8)).le.trans hY
  have hdiv : L/Real.log w ≤ (2*l)/Real.log w := div_le_div_of_nonneg_right hLl hlog.le
  have hdl : 0 < L/Real.log w := div_pos hL hlog
  have hdu : 0 < (2*l)/Real.log w := by positivity
  have hsq : (L/Real.log w)^2 ≤ ((2*l)/Real.log w)^2 := by nlinarith
  have hnum : (x^2/8)*(c0/Real.log w) ≤ Y*V0 :=
    mul_le_mul hY hV (by positivity) hY0
  calc
    _ = ((x^2/8)*(c0/Real.log w))/((2*l)/Real.log w)^2 := by
      field_simp [hl.ne',hlog.ne']
      ring
    _ ≤ ((x^2/8)*(c0/Real.log w))/(L/Real.log w)^2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hdl) hsq
    _ ≤ _ := div_le_div_of_nonneg_right hnum (sq_nonneg _)
end NumberTheoryLean.JacobsthalSurvivorScale


end Erdos970

end OAI
