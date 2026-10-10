import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorQuotientBounds
import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileExistence

namespace OAI

/-! Part (2) of the manuscript's free matching proposition on the certified disk. -/

namespace DefocusingNLS.ProfileCertificate
open ExteriorCertificate

theorem disk_free_exterior (w : Metric.closedBall (0 : ℂ) (radius : ℝ))
    (z : ℝ) (hz : (centerZ : ℝ)+w.val.im ≤ z) :
    regularizedSlowSolution (-Complex.I*(((centerB : ℝ)+w.val.re : ℝ) : ℂ))
      6 (-Complex.I*(z : ℂ)) ≠ 0 ∧
    (freeProfileJ ((centerB : ℝ)+w.val.re) z).re < 43/1000 ∧
    (3 ≤ z → 0 < (freeProfileJ ((centerB : ℝ)+w.val.re) z).im) := by
  obtain ⟨hb,hZ⟩ := disk_coordinates w
  have hbl := (abs_le.mp hb).1
  have hbu := (abs_le.mp hb).2
  have hZl := (abs_le.mp hZ).1
  have hb' : |100000000*((centerB : ℝ)+w.val.re)-33477607| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> norm_num [centerB,radius] at hbl hbu ⊢ <;> linarith
  have hz' : 2704/1000 ≤ z := by
    norm_num [centerZ,radius] at hz hZl ⊢
    linarith
  refine ⟨exterior_slow_nonzero _ z hb' hz',?_,?_⟩
  · rw [freeProfileJ_eq_log_derivative _ _ (by linarith)]
    exact exterior_quotient_real_bound _ z hb' hz'
  · intro hz3
    rw [freeProfileJ_eq_log_derivative _ _ (by linarith)]
    exact exterior_quotient_imaginary_positive _ z hb' hz3

end DefocusingNLS.ProfileCertificate

end OAI
