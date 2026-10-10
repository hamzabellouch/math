import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Invariant233

theorem map_eq_of_ae_limits_of_map_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ℕ → Ω → ℝ} {Y : ℕ → Ω' → ℝ} {Z : Ω → ℝ} {W : Ω' → ℝ}
    (hX : ∀ n, AEMeasurable (X n) μ) (hY : ∀ n, AEMeasurable (Y n) ν)
    (hZ : AEMeasurable Z μ) (hW : AEMeasurable W ν)
    (hXZ : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Z ω)))
    (hYW : ∀ᵐ ω ∂ν, Tendsto (fun n => Y n ω) atTop (𝓝 (W ω)))
    (hXY : ∀ n, μ.map (X n) = ν.map (Y n)) : μ.map Z = ν.map W := by
  have h₁ := tendstoInDistribution_of_ae_tendsto hX hZ hXZ
  have h₂ := tendstoInDistribution_of_ae_tendsto hY hW hYW
  have h₃ : TendstoInDistribution X atTop W (fun _ => μ) ν :=
    { forall_aemeasurable := hX
      aemeasurable_limit := hW
      tendsto := by simpa only [hXY] using h₂.tendsto }
  exact tendstoInDistribution_unique X h₁ h₃

end Invariant233

end OAI
