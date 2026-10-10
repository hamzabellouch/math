import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieModelMetric

namespace OAI

/-! # Comparing the two compatible metrics used in height rigidity -/

noncomputable section
namespace PolycyclicRecognition

/-- Any two proper, compatible, left-invariant chain metrics on the same
group have affine comparison bounds. This is applied to the fixed metric
and the chosen Riemannian metric, with the identity map on the group. -/
theorem ProperChainMetric.compare
    {G : Type} [Group G] [TopologicalSpace G]
    (d₁ d₂ : ProperChainMetric G) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ ∀ x y : G,
      @dist G d₂.compatibleMetric.toPseudoMetricSpace.toDist x y ≤
        K * @dist G d₁.compatibleMetric.toPseudoMetricSpace.toDist x y + C := by
  let := d₁.compatibleMetric
  let := d₁.proper_compatibleMetric
  let := d₁.isometric_compatibleMetric
  let len : G → ℝ := fun x => @dist G d₂.compatibleMetric.toPseudoMetricSpace.toDist 1 x
  have hcont : Continuous len := by
    let := d₂.compatibleMetric
    exact continuous_const.dist continuous_id
  let chains := d₁.chains_compatibleMetric
  obtain ⟨D, hD⟩ := (isCompact_closedBall (1 : G) chains.step).bddAbove_image hcont.continuousOn
  let b := max D 0
  have hb : 0 ≤ b := le_max_right _ _
  have hstep (x y : G) (hxy : dist x y ≤ chains.step) :
      @dist G d₂.compatibleMetric.toPseudoMetricSpace.toDist x y ≤ b := by
    have hx : x⁻¹ * y ∈ Metric.closedBall (1 : G) chains.step := by
      simpa only [Metric.mem_closedBall, dist_comm (x⁻¹ * y), dist_one_groupDifference] using hxy
    have hz : len (x⁻¹ * y) ≤ D := hD (Set.mem_image_of_mem _ hx)
    have hid : len (x⁻¹ * y) =
        @dist G d₂.compatibleMetric.toPseudoMetricSpace.toDist x y := by
      let := d₂.compatibleMetric
      let := d₂.isometric_compatibleMetric
      exact dist_one_groupDifference x y
    rw [hid] at hz
    exact hz.trans (le_max_left _ _)
  refine ⟨b * chains.slope, b * chains.error, mul_nonneg hb chains.slope_nonneg,
    mul_nonneg hb chains.error_nonneg, ?_⟩
  exact @LinearMetricChains.coarseLipschitz G G
    d₁.compatibleMetric.toPseudoMetricSpace d₂.compatibleMetric.toPseudoMetricSpace
    chains id b hb hstep

end PolycyclicRecognition

end

end OAI
