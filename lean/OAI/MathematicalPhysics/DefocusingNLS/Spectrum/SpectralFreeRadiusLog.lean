import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeShootingData

namespace OAI

namespace DefocusingNLS

theorem spectralFreeRadius_log (r : ℝ) (hr : 3 ≤ r) :
    max 0 (Real.log 4/2) < Real.log r := by
  have h1 : 1 < r := by linarith
  have h2 : 2 < r := by linarith
  apply max_lt (Real.log_pos h1)
  have he : Real.log (4 : ℝ)/2 = Real.log 2 := by
    rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]
    ring
  rw [he]
  exact Real.log_lt_log (by norm_num) h2

end DefocusingNLS

end OAI
