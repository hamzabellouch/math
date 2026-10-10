import OAI.Geometry.RCD.Metric.PositiveCompactCoreApproximation
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

namespace OAI

/-! # One bounded positive core sequence converging pointwise almost everywhere -/

open Set Filter MeasureTheory Topology
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.positive_core_ae_limit {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    [IsFiniteMeasureOnCompacts (hausdorff n X)] {Ω : Set X} (hΩ : IsOpen Ω)
    (φ : X → ℝ) {L B : ℝ≥0} (hφ : LipschitzWith L φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) (hφ0 : ∀ x, 0 ≤ φ x) (hφB : ∀ x, |φ x| ≤ B) :
    ∃ u : ℕ → SobolevSpace (hausdorff n X) hX.quadratic,
      (∀ k, u k ∈ compactLaplacianCore (hausdorff n X) hX.quadratic Ω) ∧
      (∀ k, ∀ᵐ x ∂hausdorff n X,
        0 ≤ SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x ∧
          |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x| ≤ B) ∧
      Tendsto u atTop (𝓝 (SobolevSpace.ofLipschitzCompact (hausdorff n X) hX.quadratic hφ hφc)) ∧
      (∀ᵐ x ∂hausdorff n X, Tendsto
        (fun k => SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x)
        atTop (𝓝 (φ x))) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  obtain ⟨u,hu,hb,hc⟩ := hX.positive_compact_core_approximation hn hΩ φ hφ hφc hφs hφ0 hφB
  have hc' := ((SobolevSpace.toLpCLM μ Q).continuous.tendsto _).comp hc
  obtain ⟨ι,hι,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hc').exists_seq_tendsto_ae
  refine ⟨fun k => u (ι k),fun k => hu (ι k),fun k => hb (ι k),hc.comp hι.tendsto_atTop,?_⟩
  filter_upwards [hae,SobolevSpace.ofLipschitzCompact_coe μ Q hφ hφc] with x hx he
  change Tendsto (fun k => SobolevSpace.toLp μ Q (u (ι k)) x) atTop
    (𝓝 (SobolevSpace.toLp μ Q (SobolevSpace.ofLipschitzCompact μ Q hφ hφc) x)) at hx
  rwa [he] at hx

end RegularPointCoordinates

end

end OAI
