import OAI.Geometry.RCD.Heat.KernelHeatGeneratorDerivative

namespace OAI

/-! # Positive-time heat values determine the initial L2 datum -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (Q : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ Q ker)

theorem kernelHeat_initial_unique (f g : Lp ℝ 2 μ)
    (h : ∀ t : ℝ, 0 < t → ∀ x, kernelHeat μ Q hk t f x = kernelHeat μ Q hk t g x) :
    f = g := by
  have he : (fun t => heatAt μ Q t f) =ᶠ[𝓝[>] (0:ℝ)] fun t => heatAt μ Q t g := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    apply Lp.ext
    have hfg : kernelHeat μ Q hk t f =ᵐ[μ] kernelHeat μ Q hk t g :=
      Eventually.of_forall (h t ht)
    exact (kernelHeat_represents_L2 μ Q hk ht f).symm.trans
      (hfg.trans (kernelHeat_represents_L2 μ Q hk ht g))
  have hf : Tendsto (fun t => heatAt μ Q t f) (𝓝[>] (0:ℝ)) (𝓝 (heatAt μ Q 0 f)) :=
    ((heatAt_continuous μ Q f).tendsto 0).mono_left inf_le_left
  have hg : Tendsto (fun t => heatAt μ Q t g) (𝓝[>] (0:ℝ)) (𝓝 (heatAt μ Q 0 g)) :=
    ((heatAt_continuous μ Q g).tendsto 0).mono_left inf_le_left
  have hh := tendsto_nhds_unique hf (hg.congr' he.symm)
  simpa only [heatAt_zero,one_apply_eq_self] using hh

end RegularPointCoordinates

end

end OAI
