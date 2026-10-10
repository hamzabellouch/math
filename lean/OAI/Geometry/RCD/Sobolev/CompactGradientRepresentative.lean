import OAI.Geometry.RCD.Sobolev.BoundedGradientLipschitz

namespace OAI

/-! # Compact Lipschitz representatives from bounded weak gradients -/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.compact_lipschitz_of_gradient {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (u : SobolevSpace (hausdorff n X) hX.quadratic) (L : ℝ≥0)
    (hL : ∀ᵐ x ∂hausdorff n X, SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic u x ≤ L)
    (p : X) (R : ℝ)
    (hz : ∀ᵐ x ∂hausdorff n X, R < dist p x →
      SobolevSpace.toLp (hausdorff n X) hX.quadratic u x = 0) :
    ∃ v : X → ℝ, LipschitzWith L v ∧ HasCompactSupport v ∧
      tsupport v ⊆ closedBall p R ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] v := by
  let μ := hausdorff n X
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : μ.IsOpenPosMeasure := hX.openPos K n
  obtain ⟨v, hv, hrep⟩ := hX.lipschitz_of_bounded_gradient K n hn
    (SobolevSpace.minimalSlope_isRelaxed μ hX.quadratic u) L hL
  have hzero : v =ᵐ[μ.restrict (closedBall p R)ᶜ] fun _ => 0 := by
    apply (ae_restrict_iff' measurableSet_closedBall.compl).mpr
    filter_upwards [hz, hrep] with x hx hr hxc
    exact hr.symm.trans (hx (by simpa only [mem_compl_iff, mem_closedBall, not_le, dist_comm] using hxc))
  have heq := Measure.eqOn_open_of_ae_eq hzero isClosed_closedBall.isOpen_compl
    hv.continuous.continuousOn continuous_const.continuousOn
  have hs : tsupport v ⊆ closedBall p R := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hnot
    exact hx (heq hnot)
  exact ⟨v, hv, (isCompact_closedBall p R).of_isClosed_subset (isClosed_tsupport _) hs, hs, hrep⟩

end RegularPointCoordinates

end

end OAI
