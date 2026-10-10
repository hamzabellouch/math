import OAI.Geometry.RCD.Heat.HeatKernelRows
import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Pointwise positive-time differentiation of the actual kernel heat flow

A fixed positive-time L2 kernel row turns the L2 heat derivative into a
pointwise derivative. No almost-everywhere choice in the time variable is
needed.
-/

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {p : ℝ → X → X → ℝ} (hp : IsContinuousHeatKernel μ hQ p)

theorem kernelHeat_add {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (f : Lp ℝ 2 μ) (x : X) :
    kernelHeat μ hQ hp (s+t) f x = kernelHeat μ hQ hp t (heatAt μ hQ s f) x := by
  unfold kernelHeat
  rw [← heatKernelRow_evolves μ hQ hp hs ht,heatAt_inner]

theorem kernelHeat_weakLaplacian_hasDerivAt (u : SobolevSpace μ hQ) (d : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ hQ u d) {t : ℝ} (ht : 0 < t) (x : X) :
    HasDerivAt (fun s => kernelHeat μ hQ hp s (SobolevSpace.toLp μ hQ u) x)
      (kernelHeat μ hQ hp t d x) t := by
  let a := t/2
  have ha : 0 < a := half_pos ht
  have hat : a < t := by dsimp [a]; linarith
  have hder := (hasDerivAt_const t (heatKernelRow μ hQ hp a x)).inner ℝ
    ((heat_weakLaplacian_hasDerivAt μ hQ u d hd (sub_pos.mpr hat)).scomp t
      ((hasDerivAt_id t).sub_const a))
  have hder' : HasDerivAt
      (fun s => inner ℝ (heatKernelRow μ hQ hp a x)
        (heatAt μ hQ (s-a) (SobolevSpace.toLp μ hQ u)))
      (inner ℝ (heatKernelRow μ hQ hp a x) (heatAt μ hQ (t-a) d)) t := by
    simpa only [inner_zero_left,add_zero,one_smul,Function.comp_def,id_eq] using hder
  have he : kernelHeat μ hQ hp t d x =
      inner ℝ (heatKernelRow μ hQ hp a x) (heatAt μ hQ (t-a) d) := by
    simpa only [sub_add_cancel,kernelHeat] using kernelHeat_add μ hQ hp (sub_pos.mpr hat) ha d x
  rw [he]
  apply hder'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hat] with s hs
  simpa only [sub_add_cancel,kernelHeat] using
    (kernelHeat_add μ hQ hp (sub_pos.mpr hs) ha (SobolevSpace.toLp μ hQ u) x)

end RegularPointCoordinates

end

end OAI
