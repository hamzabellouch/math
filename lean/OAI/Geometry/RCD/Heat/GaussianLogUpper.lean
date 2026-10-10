import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

/-! # Logarithmic upper bounds with a polynomial volume normalization -/

namespace RegularPointCoordinates

theorem gaussian_log_upper {k C c V t a ε : ℝ} {n : ℕ}
    (hk : 0 < k) (hC : 0 < C) (hc : 0 < c) (ht : 0 < t) (hε : 0 ≤ ε)
    (hV : c*(Real.sqrt t)^n ≤ V)
    (hbound : k ≤ C/V*Real.exp a) :
    ε*Real.log k ≤ ε*Real.log (C/c) - (n:ℝ)*ε/2*Real.log t + ε*a := by
  have hp : 0 < c*(Real.sqrt t)^n := mul_pos hc (pow_pos (Real.sqrt_pos.mpr ht) n)
  have hv : 0 < V := hp.trans_le hV
  have hvol := Real.log_le_log hp hV
  rw [Real.log_mul hc.ne' (pow_pos (Real.sqrt_pos.mpr ht) n).ne',Real.log_pow,
    Real.log_sqrt ht.le] at hvol
  have hlog := Real.log_le_log hk hbound
  rw [Real.log_mul (div_pos hC hv).ne' (Real.exp_ne_zero _),Real.log_div hC.ne' hv.ne',
    Real.log_exp] at hlog
  rw [Real.log_div hC.ne' hc.ne']
  have h := mul_le_mul_of_nonneg_left hlog hε
  have h' := mul_le_mul_of_nonneg_left hvol hε
  nlinarith only [h,h']

end RegularPointCoordinates

end OAI
