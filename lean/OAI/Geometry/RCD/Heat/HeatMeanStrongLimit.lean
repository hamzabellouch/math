import OAI.Geometry.RCD.Harmonic.L2ProbabilityPairing
import OAI.Geometry.RCD.Heat.KernelHeatL2Representation

namespace OAI

/-! # The original function is the uniform mean limit of its heat regularizations -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (Q : QuadraticCheegerEnergy μ)

theorem heat_means_uniform_limit {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ Q ker)
    (ν : Y → Measure X) [∀ y, IsProbabilityMeasure (ν y)]
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hν : ∀ y, ν y ≤ C • μ)
    (f : Lp ℝ 2 μ) (U : X → ℝ) (hU : f =ᵐ[μ] U)
    (s : ℕ → ℝ) (hs : ∀ k, 0 < s k) (hs0 : Tendsto s atTop (𝓝 0)) :
    TendstoUniformly (fun k y => ∫ x, kernelHeat μ Q hk (s k) f x ∂ν y)
      (fun y => ∫ x, U x ∂ν y) atTop := by
  have hheat : Tendsto (fun k => heatAt μ Q (s k) f) atTop (𝓝 f) := by
    simpa only [Function.comp_apply,heatAt_zero,one_apply_eq_self] using!
      ((heatAt_continuous μ Q f).tendsto 0).comp hs0
  have hlim := uniform_l2_probability_pairing μ ν hC hν (fun k => heatAt μ Q (s k) f) f hheat
  have heq (k : ℕ) (y : Y) :
      (∫ x, kernelHeat μ Q hk (s k) f x ∂ν y) = ∫ x, heatAt μ Q (s k) f x ∂ν y :=
    integral_congr_ae ((Measure.absolutelyContinuous_of_le_smul (hν y)).ae_eq
      (kernelHeat_represents_L2 μ Q hk (hs k) f))
  have heqU (y : Y) : (∫ x, U x ∂ν y) = ∫ x, f x ∂ν y :=
    integral_congr_ae ((Measure.absolutelyContinuous_of_le_smul (hν y)).ae_eq hU.symm)
  simpa only [heq,heqU] using hlim

end RegularPointCoordinates

end

end OAI
