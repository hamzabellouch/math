import OAI.Geometry.RCD.Heat.ContinuousKernelLog

namespace OAI

/-! # The exact constant shift of the kernel logarithm -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [CompactSpace X]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (μ : Measure Y) [IsProbabilityMeasure μ]

theorem continuousKernelLog_shift (K : C(X × Y, ℝ)) {m : ℝ} (hm : 0 < m)
    (hK : ∀ x y, m ≤ K (x,y)) (f g : C(Y, ℝ)) (c : ℝ)
    (hfg : ∀ y, f y = g y+c) (x : X) :
    continuousKernelLog μ K hm hK f x = continuousKernelLog μ K hm hK g x+c := by
  change Real.log (∫ y, K (x,y)*Real.exp (f y) ∂μ) =
    Real.log (∫ y, K (x,y)*Real.exp (g y) ∂μ)+c
  have he : (fun y => K (x,y)*Real.exp (f y)) =
      fun y => Real.exp c*(K (x,y)*Real.exp (g y)) := by
    funext y
    rw [hfg y,Real.exp_add]
    ring
  rw [he,integral_const_mul,Real.log_mul (Real.exp_pos c).ne'
    (continuous_kernel_exp_integral_pos μ K g hm hK x).ne',Real.log_exp]
  ring

end RegularPointCoordinates

end

end OAI
