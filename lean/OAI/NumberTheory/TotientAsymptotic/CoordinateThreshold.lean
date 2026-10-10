import OAI.NumberTheory.TotientAsymptotic.QuarterPowerBudget
import OAI.NumberTheory.TotientAsymptotic.CoordinateUniformBudget

namespace OAI

/-! An effective threshold for the logarithmic budget in the row estimate. -/
noncomputable section
namespace TotientAsymptotic

def coordinateBudgetConstant (F : ℝ) : ℝ := 10000*(F+31)^2

lemma coordinate_log_square_bound {b : ℝ} (hb : 1 ≤ b) :
    (Real.log (b+4))^2 ≤ 48*Real.sqrt b := by
  have hb0 : 0 ≤ b := by linarith
  have hl : 0 ≤ Real.log (b+4) := Real.log_nonneg (by linarith)
  have hlog := Real.log_le_rpow_div (show 0 ≤ b+4 by linarith) (by norm_num : (0:ℝ)<1/4)
  have hq : ((b+4)^(1/4:ℝ))^2=Real.sqrt (b+4) := by
    rw [pow_two,← Real.rpow_add (by linarith : 0 < b+4),Real.sqrt_eq_rpow]
    norm_num
  have hroot : Real.sqrt (b+4) ≤ 3*Real.sqrt b := by
    apply (Real.sqrt_le_iff).mpr ⟨by positivity,?_⟩
    nlinarith only [Real.sq_sqrt hb0,hb]
  have hs : (Real.log (b+4))^2 ≤ 16*Real.sqrt (b+4) := by
    have hp := Real.rpow_nonneg (show 0 ≤ b+4 by linarith) (1/4:ℝ)
    nlinarith only [hlog,hq,hl,hp]
  linarith only [hs,hroot]

lemma coordinate_budget_constant_pos {F : ℝ} (hF : 0 ≤ F) :
    0 < coordinateBudgetConstant F := by
  unfold coordinateBudgetConstant
  have hp : 0 < F+31 := by linarith
  positivity

lemma coordinate_log_budget_bound {b F : ℝ} (hb : 1 ≤ b) (hF : 0 ≤ F) :
    100*(Real.log (b+4)+F+30)^2 ≤ coordinateBudgetConstant F*Real.sqrt b := by
  have hlog := coordinate_log_square_bound hb
  have hs : 1 ≤ Real.sqrt b := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hb)
  have hl : 0 ≤ Real.log (b+4) := Real.log_nonneg (by linarith)
  have hsum : (Real.log (b+4)+F+30)^2 ≤ 2*(Real.log (b+4))^2+2*(F+30)^2 := by
    nlinarith only [sq_nonneg (Real.log (b+4)-(F+30))]
  have hc : 9600+200*(F+30)^2 ≤ coordinateBudgetConstant F := by
    unfold coordinateBudgetConstant
    nlinarith only [hF,sq_nonneg F]
  have hmul := mul_le_mul_of_nonneg_left hs (sq_nonneg (F+30))
  have hfinal := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg b)
  nlinarith only [hlog,hsum,hmul,hfinal]

lemma coordinate_threshold_budget {b F δ : ℝ} (hb : 1 ≤ b) (hF : 0 ≤ F) (hδ : 0 < δ)
    (hthreshold : (coordinateBudgetConstant F/δ)^(4/3:ℝ) ≤ b) :
    100*(Real.log (b+4)+F+30)^2 ≤ δ*b :=
  four_thirds_threshold_budget hb hF hδ hthreshold

end TotientAsymptotic

end

end OAI
