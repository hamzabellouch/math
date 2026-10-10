import OAI.Geometry.RCD.Heat.KernelHeatGeneratorDerivative

namespace OAI

/-! # The time generator is the weak spatial Laplacian of the same heat value -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {p : ℝ → X → X → ℝ} (hp : IsContinuousHeatKernel μ hQ p)

theorem kernelHeat_spatial_source (f : Lp ℝ 2 μ) {t : ℝ} (ht : 0 < t) :
    ∃ (u : SobolevSpace μ hQ) (d : Lp ℝ 2 μ),
      (kernelHeat μ hQ hp t f =ᵐ[μ] SobolevSpace.toLp μ hQ u) ∧
      IsWeakLaplacian μ hQ u d ∧
      (kernelHeatGeneratorSource μ hQ hp t f =ᵐ[μ] d) := by
  refine ⟨heatSobolev μ hQ t ht f,-heatGenerator μ hQ t ht f,?_,
    heatSobolev_weak_laplacian μ hQ t ht f,?_⟩
  · simpa only [heatSobolev_toLp] using kernelHeat_represents_L2 μ hQ hp ht f
  · filter_upwards [kernelHeatGeneratorSource_represents μ hQ hp ht f,
      Lp.coeFn_neg (heatGenerator μ hQ t ht f)] with x hx hn
    rw [heatGeneratorAt_of_pos μ hQ t ht] at hx
    exact hx.trans hn.symm

end RegularPointCoordinates

end

end OAI
