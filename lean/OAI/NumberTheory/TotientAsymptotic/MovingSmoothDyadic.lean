import OAI.NumberTheory.TotientAsymptotic.MovingSmoothCount
import OAI.NumberTheory.TotientAsymptotic.DyadicCoordinateRow

namespace OAI

/-! A moving smoothness condition on a totient transfers to its dyadic slice. -/
noncomputable section
namespace TotientAsymptotic

lemma B_mono {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) : B x ≤ B y :=
  Real.log_le_log (Real.log_pos hx) (Real.log_le_log (by linarith) hxy)

lemma relative_smooth_at_dyadic {v n : ℕ} (hv : 2 ≤ v) (hB : 1 ≤ B (v:ℝ))
    (hsmooth : (largestPrimeFactor n:ℝ) ≤ Real.exp (Real.log v/(1000*B v))) :
    largestPrimeFactor n ≤ movingSmoothCutoff ((2:ℝ)^(Nat.clog 2 v)) := by
  have hd := dyadic_nat_bounds (show 1 < v by omega)
  have hv1 : (1:ℝ) < v := by exact_mod_cast (show 1 < v by omega)
  have hBx := B_mono hv1 hd.2.2
  have hloss := dyadic_coordinate_loss hv
  have hl : Real.log (v:ℝ) ≤ Real.log ((2:ℝ)^(Nat.clog 2 v)) :=
    Real.log_le_log (by linarith) hd.2.2
  have hlogv : 0 ≤ Real.log (v:ℝ) := (Real.log_pos hv1).le
  have hBv : 0 < B (v:ℝ) := by linarith only [hB]
  have hBX : 0 < B ((2:ℝ)^(Nat.clog 2 v)) := hBv.trans_le hBx
  have hr : Real.log v/(1000*B v) ≤
      Real.log ((2:ℝ)^(Nat.clog 2 v))/(500*B ((2:ℝ)^(Nat.clog 2 v))) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hd : 500*B ((2:ℝ)^(Nat.clog 2 v)) ≤ 1000*B v := by linarith only [hloss,hB]
    exact mul_le_mul hl hd (by positivity) (by linarith)
  apply Nat.le_floor
  exact hsmooth.trans (Real.exp_le_exp.mpr hr)

end TotientAsymptotic

end

end OAI
