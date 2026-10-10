import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OAI

/-! # Uniform interior control of the scaled logarithmic time error -/

namespace RegularPointCoordinates

theorem scaled_log_time_error {n k ε δ s t : ℝ} (hn : 0≤n) (hk : 0≤k)
    (hε : 0≤ε) (hε1 : ε≤1) (hδ : 0<δ) (hδs : δ≤ s) (hst : s≤t) :
    n*ε*Real.log (t/s)+n*k*ε^2*(t-s)/2 ≤
      ε*(n/δ+n*k/2)*(t-s) := by
  have hs : 0<s := hδ.trans_le hδs
  have ht : 0<t := hs.trans_le hst
  have hlog := Real.log_le_sub_one_of_pos (div_pos ht hs)
  have he : t/s-1=(t-s)/s := by field_simp
  rw [he] at hlog
  have hdiv : (t-s)/s≤(t-s)/δ :=
    div_le_div_of_nonneg_left (sub_nonneg.mpr hst) hδ hδs
  have hfirst := mul_le_mul_of_nonneg_left (hlog.trans hdiv) (mul_nonneg hn hε)
  have heps : ε^2≤ε := by nlinarith only [hε,hε1]
  have hsecond := mul_le_mul_of_nonneg_left heps
    (show 0≤n*k*(t-s)/2 by positivity)
  calc
    _ ≤ n*ε*((t-s)/δ)+(n*k*(t-s)/2)*ε := by nlinarith only [hfirst,hsecond]
    _ = _ := by ring

end RegularPointCoordinates

end OAI
