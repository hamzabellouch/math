import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! The stopping lower-energy bound makes a quadratic per-top far
estimate summable linearly in the selected energy. -/
noncomputable section
namespace LipschitzHilbert

theorem quadratic_far_bound_linear {x E sigma A K : ℝ}
    (hE : 0≤E) (hK : 0≤K)
    (hfar : x^2≤K*(sigma^2*A)*E) (hstop : sigma^2*A≤2*E) :
    x≤Real.sqrt (2*K)*E := by
  have hb := hfar.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstop hK) hE)
  have hr : 0≤Real.sqrt (2*K)*E := mul_nonneg (Real.sqrt_nonneg _) hE
  have hs : (Real.sqrt (2*K)*E)^2=2*K*E^2 := by
    rw [mul_pow,Real.sq_sqrt (mul_nonneg (by norm_num) hK)]
  nlinarith

end LipschitzHilbert

end

end OAI
