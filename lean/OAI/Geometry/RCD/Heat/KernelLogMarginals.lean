import OAI.Geometry.RCD.Heat.KernelScalingFixedPoint
import OAI.Geometry.RCD.Heat.KernelLogConstants

namespace OAI

/-! # Exact logarithmic marginal equations up to one scalar

The fixed point in continuous differences lifts to logarithmic weights.
One marginal is exact and the other has a constant logarithmic value.
-/

open Set MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem positive_kernel_log_marginals (K : C(X × Y, ℝ)) {m M : ℝ}
    (hm : 0 < m) (hK : ∀ x y, m ≤ K (x,y)) (hM : ∀ x y, K (x,y) ≤ M)
    (x₀ : X) (y₀ : Y) :
    ∃ (f : C(X, ℝ)) (g : C(Y, ℝ)) (c : ℝ),
      (∀ x, f x+continuousKernelLog ν K hm hK g x=c) ∧
      (∀ y, g y+continuousKernelLog μ (transposeContinuousKernel K) hm
        (fun y x => hK x y) f y=0) := by
  obtain ⟨d,hd⟩ := positive_kernel_difference_fixedPoint μ ν K hm hK hM x₀ y₀
  let f := differenceValue X d x₀
  let g := -continuousKernelLog μ (transposeContinuousKernel K) hm (fun y x => hK x y) f
  let e := continuousDifference Y g
  let g₀ := differenceValue Y e y₀
  have hfixed : continuousDifference X (-continuousKernelLog ν K hm hK g₀)=d := hd
  have hshift : ∀ x, continuousKernelLog ν K hm hK g₀ x =
      continuousKernelLog ν K hm hK g x - g y₀ := by
    intro x
    apply continuousKernelLog_shift ν K hm hK g₀ g (-g y₀)
    intro y
    change g y - g y₀ = g y + -g y₀
    ring
  refine ⟨f,g,continuousKernelLog ν K hm hK g x₀,?_,?_⟩
  · intro x
    have he := congrArg (fun h : ContinuousDifference X => h.val (x,x₀)) hfixed
    change -continuousKernelLog ν K hm hK g₀ x -
      -continuousKernelLog ν K hm hK g₀ x₀ = f x at he
    rw [hshift x,hshift x₀] at he
    linarith
  · intro y
    change -continuousKernelLog μ (transposeContinuousKernel K) hm (fun y x => hK x y) f y +
      continuousKernelLog μ (transposeContinuousKernel K) hm (fun y x => hK x y) f y=0
    ring

end RegularPointCoordinates

end

end OAI
