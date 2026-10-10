import OAI.Geometry.RCD.Heat.KernelHeatL2Representation

namespace OAI

/-! # Pointwise time continuity of kernel heat for every L2 datum -/

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {p : ℝ → X → X → ℝ} (hp : IsContinuousHeatKernel μ hQ p)

theorem kernelHeat_continuousAt_time (f : Lp ℝ 2 μ) {t : ℝ} (ht : 0 < t) (x : X) :
    ContinuousAt (fun s => kernelHeat μ hQ hp s f x) t := by
  let a := t/2
  have ha : 0 < a := half_pos ht
  have hat : a < t := by dsimp [a]; linarith
  have hc : Continuous (fun s => inner ℝ (heatKernelRow μ hQ hp a x) (heatAt μ hQ (s-a) f)) :=
    continuous_const.inner ((heatAt_continuous μ hQ f).comp (continuous_id.sub continuous_const))
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hat] with s hs
  simpa only [sub_add_cancel,kernelHeat] using
    (kernelHeat_add μ hQ hp (sub_pos.mpr hs) ha f x)

end RegularPointCoordinates

end

end OAI
