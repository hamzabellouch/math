import OAI.Analysis.IrrationalRotation.Rotation.CircleBackgroundCost
import OAI.Analysis.IrrationalRotation.Analysis.BackgroundTransfer

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace Invariant233.BackgroundCost

theorem exists_background_coboundary (θ : ℝ) (hθ : Irrational θ) :
    ∃ g b : Circle → ℝ, Measurable g ∧ Measurable b ∧
      ContinuousOn g ({0}ᶜ : Set Circle) ∧ (∀ x, 1 / 2 ≤ g x) ∧
      Tendsto g (𝓝[≠] (0 : Circle)) atTop ∧ Integrable g circleMeasure ∧
      g =ᵐ[circleMeasure] (fun x => 1 + b (x + (θ : Circle)) - b x) := by
  obtain ⟨d⟩ := exists_backgroundBumpData θ hθ
  exact ⟨backgroundCost d, backgroundTransferSum d, measurable_backgroundCost d,
    measurable_backgroundTransferSum d, continuousOn_backgroundCost d,
    backgroundCost_ge_half d, tendsto_backgroundCost_atTop d,
    integrable_backgroundCost d, backgroundCost_ae_coboundary d⟩

end Invariant233.BackgroundCost

end

end OAI
