import OAI.Geometry.RCD.Sobolev.RadialLocalSobolev
import OAI.Geometry.RCD.Metric.SupportedL2Continuity
import OAI.Geometry.RCD.Metric.InjectiveHilbertMeasurable
import Mathlib.MeasureTheory.Measure.SeparableMeasure

namespace OAI

/-! # Measurable Sobolev families from continuous compact local values -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (Q : QuadraticCheegerEnergy μ)

variable [TopologicalSpace Y] [FirstCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y]

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem radialLocalSobolev_toLp_continuous (z : X) {r : ℝ} (hr : 0 < r)
    (H : Y → X → ℝ) (L A : ℝ≥0)
    (hL : ∀ t, LipschitzOnWith L (H t) (closedBall z (2*r)))
    (hA : ∀ t, ∀ x ∈ closedBall z (2*r), |H t x| ≤ A)
    (hc : ∀ x ∈ closedBall z (2*r), Continuous (fun t => H t x)) :
    Continuous (fun t => SobolevSpace.toLp μ Q (radialLocalSobolev μ Q z hr (hL t) (hA t))) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply supported_L2_tendsto μ measurableSet_closedBall
    (isCompact_closedBall z (2*r)).measure_lt_top.ne
    _ _ (fun s x => radialCutoff z r x*H s x) (fun x => radialCutoff z r x*H t x)
    (fun s => radialLocalSobolev_coe μ Q z hr (hL s) (hA s))
    (radialLocalSobolev_coe μ Q z hr (hL t) (hA t)) A.coe_nonneg
    (fun s => (radial_local_lipschitz_cutoff z hr (hL s) (hA s)).2)
    (radial_local_lipschitz_cutoff z hr (hL t) (hA t)).2
  · intro s x hx
    rw [radialCutoff_eq_zero z hr
      (le_of_lt (by simpa only [mem_closedBall,not_le,dist_comm] using hx)),zero_mul]
  · intro x hx
    rw [radialCutoff_eq_zero z hr
      (le_of_lt (by simpa only [mem_closedBall,not_le,dist_comm] using hx)),zero_mul]
  · intro x hx
    exact ((hc x hx).continuousAt).const_mul _

theorem radialLocalSobolev_stronglyMeasurable
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (z : X) {r : ℝ} (hr : 0 < r) (H : Y → X → ℝ) (L A : ℝ≥0)
    (hL : ∀ t, LipschitzOnWith L (H t) (closedBall z (2*r)))
    (hA : ∀ t, ∀ x ∈ closedBall z (2*r), |H t x| ≤ A)
    (hc : ∀ x ∈ closedBall z (2*r), Continuous (fun t => H t x)) :
    StronglyMeasurable (fun t => radialLocalSobolev μ Q z hr (hL t) (hA t)) := by
  apply injective_hilbert_image_stronglyMeasurable (SobolevSpace.toLpCLM μ Q)
    (fun f g h => Subtype.ext h)
  exact (radialLocalSobolev_toLp_continuous μ Q z hr H L A hL hA hc).stronglyMeasurable

omit [TopologicalSpace Y] [FirstCountableTopology Y] [BorelSpace Y]
  [BorelSpace X] [ProperSpace X] [IsFiniteMeasureOnCompacts μ] in
theorem sobolev_limit_aestronglyMeasurable [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (ν : Measure Y) (u : ℕ → Y → SobolevSpace μ Q) (v : Y → SobolevSpace μ Q)
    (hu : ∀ k, AEStronglyMeasurable (u k) ν)
    (hc : ∀ᵐ t ∂ν, Tendsto (fun k => SobolevSpace.toLp μ Q (u k t)) atTop
      (𝓝 (SobolevSpace.toLp μ Q (v t)))) : AEStronglyMeasurable v ν := by
  apply injective_hilbert_image_aestronglyMeasurable (SobolevSpace.toLpCLM μ Q)
    (fun f g h => Subtype.ext h) v ν
  apply aestronglyMeasurable_of_tendsto_ae atTop _ hc
  intro k
  exact (SobolevSpace.toLpCLM μ Q).continuous.comp_aestronglyMeasurable (hu k)

end RegularPointCoordinates

end

end OAI
