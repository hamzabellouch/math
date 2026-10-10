import OAI.Geometry.RCD.Sobolev.BoundedGradientLipschitz

namespace OAI

/-! # Local Lipschitz representatives from shrinking-ball averages -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] {μ : Measure X} [IsLocallyFiniteMeasure μ]
  [IsUnifLocDoublingMeasure μ]

/-- The averaging estimate need only hold at sufficiently small radii for
each pair of centers in the chosen region. -/
theorem exists_lipschitz_of_local_average_bound (u : X → ℝ) (hu : LocallyIntegrable u μ)
    {S : Set X} (hS : MeasurableSet S) (L : ℝ≥0)
    (h : ∀ x ∈ S, ∀ y ∈ S, ∀ᶠ r in 𝓝[>] (0:ℝ),
      |(⨍ z in closedBall x r, u z ∂μ)-(⨍ z in closedBall y r, u z ∂μ)| ≤
        L*(dist x y+2*r)) :
    ∃ v : X → ℝ, LipschitzWith L v ∧ u =ᵐ[μ.restrict S] v := by
  let T := {x : X | Tendsto (fun r : ℝ => ⨍ z in closedBall x r, u z ∂μ)
    (𝓝[>] 0) (𝓝 (u x))}
  have hT : ∀ᵐ x ∂μ, x ∈ T := by
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average μ hu (1:ℝ)] with x hx
    exact hx (fun _ : ℝ => x) id tendsto_id (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [mem_closedBall,dist_self,one_mul]
      exact le_of_lt hr)
  have hl : LipschitzOnWith L u (S ∩ T) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hc : Tendsto (fun r : ℝ => (L:ℝ)*(dist x y+2*r)) (𝓝[>] 0)
        (𝓝 ((L:ℝ)*dist x y)) := by
      have hh : Continuous (fun r : ℝ => (L:ℝ)*(dist x y+2*r)) := by fun_prop
      simpa using (hh.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    simpa only [Real.dist_eq] using
      le_of_tendsto_of_tendsto ((hx.2.sub hy.2).abs) hc (h x hx.1 y hy.1)
  obtain ⟨v,hv,he⟩ := hl.extend_real
  refine ⟨v,hv,?_⟩
  filter_upwards [ae_restrict_mem hS,ae_restrict_of_ae hT] with x hx ht
  exact he ⟨hx,ht⟩

end RegularPointCoordinates

end

end OAI
