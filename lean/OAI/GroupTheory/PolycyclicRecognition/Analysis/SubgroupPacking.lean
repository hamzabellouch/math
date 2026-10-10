import OAI.GroupTheory.PolycyclicRecognition.Analysis.FixedSlicePacking

namespace OAI

/-! # Packing on the identity slice of a closed subgroup

For segment comparison the source pivot is the identity. Haar invariance
under left translations alone bounds every pulled-back ambient ball.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Metric Set
open scoped ENNReal

variable {N G : Type*} [Group N] [Group G]
  [MeasurableSpace N] [MeasurableMul N] [TopologicalSpace N]
  [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  (ι : N →* G) (μ : Measure N) [μ.IsMulLeftInvariant]

omit [TopologicalSpace N] [IsTopologicalGroup G] in
/-- Left invariance controls all ambient balls on the identity subgroup slice. -/
theorem subgroup_ball_measure (v : N) (r : ℝ) :
    μ (ι ⁻¹' closedBall (ι v) r) = μ (ι ⁻¹' closedBall (1 : G) r) := by
  let κ : PUnit.{1} →* G := 1
  let φ : PUnit.{1} →* MulAut N := 1
  have hp (d : PUnit.{1}) : MeasurePreserving (φ d) μ μ := by
    exact MeasurePreserving.id μ
  have hc (d : PUnit.{1}) (n : N) : ι (φ d n) = κ d * ι n * (κ d)⁻¹ := by
    simp [φ, κ]
  simpa only [κ, MonoidHom.one_apply, one_mul, mul_one] using
    fixedSlice_ball_measure ι κ φ μ hp hc (1 : G) PUnit.unit v r

omit [IsTopologicalGroup G] in
/-- Every relatively compact subgroup endpoint set has a separated net
with a cardinality lower bound in terms of its Haar mass. -/
theorem exists_subgroup_separated_net (hι : Continuous ι) {K S : Set N}
    (hK : IsCompact K) (hS : S ⊆ K) {r : ℝ} (hr : 0 < r) :
    ∃ t : Finset G, (↑t : Set G) ⊆ ι '' S ∧
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧
      μ S ≤ (t.card : ℝ≥0∞) * μ (ι ⁻¹' closedBall (1 : G) r) := by
  apply exists_separated_image_net_volume_bound μ ι
    ((hK.image hι).totallyBounded.subset (image_mono hS)) hr
  rintro x ⟨v, _, rfl⟩
  exact (subgroup_ball_measure ι μ v r).le

end PolycyclicRecognition

end

end OAI
