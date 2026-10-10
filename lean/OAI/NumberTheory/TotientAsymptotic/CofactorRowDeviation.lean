import OAI.NumberTheory.TotientAsymptotic.FordCofactorCoordinates
import OAI.NumberTheory.TotientAsymptotic.CoordinateThreshold

namespace OAI

/-! Transfer a failed simplex row to the ordered coordinates of its cofactor. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma cofactor_row_deviation {n j k : ℕ} {b ω : ℝ}
    (hb : 0 ≤ b) (hω : 0 ≤ ω) (hω1 : ω ≤ 1)
    (hbudget : 4*Real.log b ≤ ω*b)
    (hhead : b-Real.log b ≤ fordPrimeCoordinate n j)
    (hrow : (1+ω)*fordPrimeCoordinate n j <
      ∑ i : Fin k,a (i.val+1)*fordPrimeCoordinate n (j+i.val+1)) :
    (1+ω/2)*b <
      ∑ i : Fin k,a (i.val+1)*fordPrimeCoordinate (fordCofactor n j) (i.val+1) := by
  have hlow := mul_le_mul_of_nonneg_left hhead (show 0 ≤ 1+ω by linarith)
  have hlog : (1+ω)*Real.log b ≤ ω*b/2 := by
    by_cases hl : 0 ≤ Real.log b
    · nlinarith only [mul_le_mul_of_nonneg_right hω1 hl,hbudget]
    · have hh : (1+ω)*Real.log b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      nlinarith only [hh,mul_nonneg hω hb]
  have hs : (1+ω/2)*b <
      ∑ i : Fin k,a (i.val+1)*fordPrimeCoordinate n (j+i.val+1) := by
    nlinarith only [hlow,hlog,hrow]
  convert hs using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [fordCofactor_coordinate]
  congr 2

lemma coordinate_threshold_head_budget {b ω F : ℝ} {k : ℕ}
    (hb : 1 ≤ b) (hω : 0 ≤ ω) (hω1 : ω ≤ 1) (hF : 0 ≤ F)
    (hbudget : 100*(Real.log (b+4)+F+30)^2 ≤ coordinateDecay ω k*b) :
    4*Real.log b ≤ ω*b := by
  have hl : 0 ≤ Real.log (b+4) := Real.log_nonneg (by linarith)
  have hlog : Real.log b ≤ Real.log (b+4) := Real.log_le_log (by linarith) (by linarith)
  have hd := mul_le_mul_of_nonneg_right (coordinate_decay_bounds (k:=k) hω hω1).2.2
    (show 0 ≤ b by linarith)
  have hsum : 30 ≤ Real.log (b+4)+F+30 := by linarith
  nlinarith only [hbudget,hd,hlog,hl,hF,hsum]

end TotientAsymptotic

end

end OAI
