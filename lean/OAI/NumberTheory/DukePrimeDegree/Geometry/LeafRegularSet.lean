import OAI.NumberTheory.DukePrimeDegree.Dynamics.LeafReturnCovariance
import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafLusin

namespace OAI

/-!
# One conull set for leaf regularity and rebasing

The measurable kernel agrees with the intrinsic leaf, is locally finite,
has positive mass in every neighborhood of the origin, and satisfies
the leafwise rebasing law outside a single measurable null set.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_rootLeaf_regular_nullset
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0) :
    ∃ N : Set (X n), MeasurableSet N ∧ μ N = 0 ∧ ∀ x ∉ N,
      intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x ∧
      IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) ∧
      (∀ r : ℝ, 0 < r → 0 < intrinsicRootLeaf hij μ x (Metric.ball 0 r)) ∧
      ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
        intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
          basedRealMeasure (intrinsicRootLeaf hij μ x) t := by
  have h : ∀ᵐ x ∂μ,
      intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x ∧
      IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) ∧
      (∀ r : ℝ, 0 < r → 0 < intrinsicRootLeaf hij μ x (Metric.ball 0 r)) ∧
      ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
        intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
          basedRealMeasure (intrinsicRootLeaf hij μ x) t := by
    filter_upwards [ae_intrinsicRootKernel_eq hij μ hfree, ae_intrinsicRootLeaf_spec hij μ hfree,
      ae_intrinsicRootLeaf_ball_pos hij μ hfree, ae_intrinsicRootLeaf_rebase hij μ hfree]
      with x hx hs hp hr
    exact ⟨hx, hs.1, hp, hr⟩
  obtain ⟨N, hbad, hN, hzero⟩ := exists_measurable_superset_of_null (ae_iff.mp h)
  refine ⟨N, hN, hzero, ?_⟩
  intro x hx
  by_contra h
  exact hx (hbad h)

end DukePrimeDegree

end

end OAI
