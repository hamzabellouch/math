import OAI.Geometry.RCD.Heat.KernelHeatL2Representation

namespace OAI

/-! # Pointwise heat differentiation for arbitrary L2 initial data -/

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {p : ℝ → X → X → ℝ} (hp : IsContinuousHeatKernel μ hQ p)

def kernelHeatGeneratorSource (t : ℝ) (f : Lp ℝ 2 μ) (x : X) : ℝ :=
  kernelHeat μ hQ hp (t/2) (-heatGeneratorAt μ hQ (t/2) f) x

theorem kernelHeat_generator_hasDerivAt (f : Lp ℝ 2 μ) {t : ℝ} (ht : 0 < t) (x : X) :
    HasDerivAt (fun s => kernelHeat μ hQ hp s f x)
      (kernelHeatGeneratorSource μ hQ hp t f x) t := by
  let a := t/2
  have ha : 0 < a := half_pos ht
  have hat : a < t := by dsimp [a]; linarith
  have hder := (hasDerivAt_const t (heatKernelRow μ hQ hp a x)).inner ℝ
    ((heatAt_hasDerivAt μ hQ (t-a) (sub_pos.mpr hat) f).scomp t
      ((hasDerivAt_id t).sub_const a))
  have hder' : HasDerivAt
      (fun s => inner ℝ (heatKernelRow μ hQ hp a x) (heatAt μ hQ (s-a) f))
      (kernelHeatGeneratorSource μ hQ hp t f x) t := by
    have he : t-a=a := by dsimp [a]; ring
    simpa only [inner_zero_left,add_zero,one_smul,Function.comp_def,id_eq,he,
      kernelHeatGeneratorSource,kernelHeat,a] using hder
  apply hder'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hat] with s hs
  simpa only [sub_add_cancel,kernelHeat] using (kernelHeat_add μ hQ hp (sub_pos.mpr hs) ha f x)

theorem kernelHeatGeneratorSource_represents {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 μ) :
    kernelHeatGeneratorSource μ hQ hp t f =ᵐ[μ] -heatGeneratorAt μ hQ t f := by
  have ha := half_pos ht
  have he : heatAt μ hQ (t/2) (-heatGeneratorAt μ hQ (t/2) f) = -heatGeneratorAt μ hQ t f := by
    rw [map_neg,heatGeneratorAt_of_pos μ hQ (t/2) ha,heatGeneratorAt_of_pos μ hQ t ht]
    have hh := heatGenerator_add μ hQ (t/2) (t/2) ha.le ha
    simp only [add_halves] at hh
    rw [hh,mul_apply_eq_comp]
  filter_upwards [kernelHeat_represents_L2 μ hQ hp ha (-heatGeneratorAt μ hQ (t/2) f),
    Lp.coeFn_neg (heatGeneratorAt μ hQ t f)] with x hx hn
  exact hx.trans ((congrArg (fun g : Lp ℝ 2 μ => g x) he).trans hn)

theorem continuous_kernelHeatGeneratorSource (t : ℝ) (x : X) :
    Continuous (fun f : Lp ℝ 2 μ => kernelHeatGeneratorSource μ hQ hp t f x) :=
  continuous_const.inner ((heatGeneratorAt μ hQ (t/2)).continuous.neg)

end RegularPointCoordinates

end

end OAI
