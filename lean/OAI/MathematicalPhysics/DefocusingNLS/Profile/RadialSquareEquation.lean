import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSquareRegularity

namespace OAI

/-! The nonsingular squared-radius equation used to bootstrap origin regularity. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radialSquareSlope_integral (k : ℕ) (a b x : ℝ) (hx : 0 ≤ x) (Q : ℝ → ℂ) :
    radialSquareSlope k a b Q x=
      (∫ t in (0 : ℝ)..1, (t : ℂ)^11*Complex.exp (Complex.I*(x*(t^2-1)/4 : ℝ))*
        radialComplexSource k a b (radialSquareProfile Q (x*t^2)))/2 := by
  unfold radialSquareSlope radialComplexAverage
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht0 : 0 ≤ t := (show t ∈ Icc (0 : ℝ) 1 by simpa using ht).1
  have hs : Real.sqrt (x*t^2)=Real.sqrt x*t := by
    rw [Real.sqrt_mul hx,Real.sqrt_sq ht0]
  simp only [radialSquareProfile,Real.sq_sqrt hx,hs]

end DefocusingNLS

end OAI
