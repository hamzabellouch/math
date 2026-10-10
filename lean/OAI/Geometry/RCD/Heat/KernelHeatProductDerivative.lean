import OAI.Geometry.RCD.Heat.KernelHeatGeneratorDerivative

namespace OAI

/-! # Product and logarithmic time derivatives for the heat bridge

The sources are the actual bounded L² heat generators.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {p : ℝ → X → X → ℝ} (hp : IsContinuousHeatKernel μ hQ p)

theorem kernelHeat_product_hasDerivAt (f g : Lp ℝ 2 μ) (T t : ℝ)
    (ht : 0 < t) (htT : t < T) (x : X) :
    HasDerivAt (fun s => kernelHeat μ hQ hp s f x * kernelHeat μ hQ hp (T-s) g x)
      (kernelHeatGeneratorSource μ hQ hp t f x * kernelHeat μ hQ hp (T-t) g x -
        kernelHeat μ hQ hp t f x * kernelHeatGeneratorSource μ hQ hp (T-t) g x) t := by
  have ha := kernelHeat_generator_hasDerivAt μ hQ hp f ht x
  have hb := (kernelHeat_generator_hasDerivAt μ hQ hp g (sub_pos.mpr htT) x).scomp t
    ((hasDerivAt_const t T).sub (hasDerivAt_id t))
  convert ha.mul hb using 1
  · rfl
  · dsimp only [Function.comp_def,smul_eq_mul]
    ring

theorem kernelHeat_log_hasDerivAt (f : Lp ℝ 2 μ) {t : ℝ} (ht : 0 < t) (x : X)
    (hx : kernelHeat μ hQ hp t f x ≠ 0) :
    HasDerivAt (fun s => Real.log (kernelHeat μ hQ hp s f x))
      (kernelHeatGeneratorSource μ hQ hp t f x / kernelHeat μ hQ hp t f x) t :=
  (kernelHeat_generator_hasDerivAt μ hQ hp f ht x).log hx

end RegularPointCoordinates

end

end OAI
