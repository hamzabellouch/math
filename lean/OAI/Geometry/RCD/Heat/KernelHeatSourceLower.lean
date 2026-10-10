import OAI.Geometry.RCD.Heat.HeatLiYau
import OAI.Geometry.RCD.Heat.KernelHeatGeneratorDerivative

namespace OAI

/-! # Pointwise lower bounds for the actual continuous heat source

The source has its own positive-time continuous representative. Full support
therefore removes the exceptional spatial set at every prescribed time.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p

theorem kernelHeat_source_lower (hK : K≤0)
    {kernel : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic kernel)
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0≤f) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A) {t : ℝ} (ht : 0<t) (x : X) :
    -(n:ℝ)*(|K|+1/t)*kernelHeat (hausdorff n X) hX.quadratic hk t f x ≤
      kernelHeatGeneratorSource (hausdorff n X) hX.quadratic hk t f x := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let := hX.openPos K n
  let H := kernelHeat μ Q hk t f
  let D := kernelHeatGeneratorSource μ Q hk t f
  let a := -(n:ℝ)*(|K|+1/t)
  have hH : Continuous H := kernelHeat_continuous μ Q hk ht f
  have hD : Continuous D := kernelHeat_continuous μ Q hk (half_pos ht) _
  have he : (fun y => min (a*H y) (D y)) =ᵐ[μ] fun y => a*H y := by
    filter_upwards [hX.heat_source_lower hn p hK f hf0 A hf ht,
      kernelHeat_represents_L2 μ Q hk ht f,
      kernelHeatGeneratorSource_represents μ Q hk ht f,
      Lp.coeFn_neg (heatGeneratorAt μ Q t f)] with y hy hh hd hneg
    apply min_eq_left
    change a*H y≤D y
    change H y=_ at hh
    change D y=_ at hd
    rw [hh,hd]
    simp only [Pi.neg_apply] at hneg ⊢
    rw [←hneg]
    exact hy
  have hsame := Measure.eq_of_ae_eq he ((hH.const_mul a).min hD) (hH.const_mul a)
  exact min_eq_left_iff.mp (congrFun hsame x)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
