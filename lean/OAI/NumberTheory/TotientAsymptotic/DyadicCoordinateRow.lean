import OAI.NumberTheory.TotientAsymptotic.RealCoordinateDeviation
import OAI.NumberTheory.TotientAsymptotic.DyadicLogGeometry

namespace OAI

/-! A relative row failure persists at the next dyadic endpoint. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma dyadic_coordinate_loss {v : ℕ} (hv : 2 ≤ v) :
    B ((2:ℝ)^(Nat.clog 2 v))-1 ≤ B (v:ℝ) := by
  have hd := dyadic_nat_bounds (show 1 < v by omega)
  have hx : (1:ℝ) < (2:ℝ)^(Nat.clog 2 v) :=
    one_lt_pow₀ (by norm_num) (by omega)
  have hmono : B ((2:ℝ)^(Nat.clog 2 v)) ≤ B (2*(v:ℝ)) := by
    apply Real.log_le_log (Real.log_pos hx)
    apply Real.log_le_log (by positivity)
    linarith only [hd.2.1]
  have hvR : (2:ℝ) ≤ v := by exact_mod_cast hv
  linarith only [hmono,double_log_double_le hvR]

lemma relative_row_at_dyadic {v k : ℕ} {ω : ℝ} (hv : 2 ≤ v)
    (hω : 0 ≤ ω) (hω1 : ω ≤ 1) (hsize : 4 ≤ ω*B ((2:ℝ)^(Nat.clog 2 v)))
    {n : ℕ} (hrow : (1+ω)*B (v:ℝ) <
      ∑ i : Fin k,a (i.val+1)*fordPrimeCoordinate n (i.val+1)) :
    (1+ω/2)*B ((2:ℝ)^(Nat.clog 2 v)) ≤
      ∑ i : Fin k,a (i.val+1)*fordPrimeCoordinate n (i.val+1) := by
  have hh := mul_le_mul_of_nonneg_left (dyadic_coordinate_loss hv)
    (show 0 ≤ 1+ω by linarith)
  nlinarith only [hh,hrow,hsize,hω1]

end TotientAsymptotic

end

end OAI
