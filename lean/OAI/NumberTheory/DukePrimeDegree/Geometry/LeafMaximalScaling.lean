import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafShortMaximal

namespace OAI

/-!
# Scaling relative bad intervals by the diagonal action

The actual canonical diagonal flow rescales root time by its exponential.
Transport and projective normalization preserve every relative mass
inequality used in the leafwise maximal argument.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma normalized_map_image_relative_bound (ν : Measure ℝ) (e : ℝ ≃ₜ ℝ)
    (J S T : Set ℝ) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (c : ℝ≥0∞) (h : c * ν S ≤ ν T) :
    c * anchorNormalize (ν.map e) J (e '' S) ≤
      anchorNormalize (ν.map e) J (e '' T) := by
  have hmap (U : Set ℝ) (hU : MeasurableSet U) : (ν.map e) (e '' U) = ν U := by
    rw [Measure.map_apply e.measurable
      (e.isOpenEmbedding.measurableEmbedding.measurableSet_image.mpr hU),
      e.injective.preimage_image]
  change c * ((ν.map e J)⁻¹ * ν.map e (e '' S)) ≤
    (ν.map e J)⁻¹ * ν.map e (e '' T)
  rw [hmap S hS, hmap T hT, mul_left_comm]
  exact mul_le_mul' le_rfl h

lemma scaling_image_closedBall_zero (a : ℝ) (ha : 0 < a) (r : ℝ) :
    (Homeomorph.mulLeft₀ a ha.ne') '' closedBall 0 r = closedBall 0 (a * r) := by
  let e := Homeomorph.mulLeft₀ a ha.ne'
  have hpre : e ⁻¹' closedBall 0 (a * r) = closedBall 0 r := by
    ext u
    simp only [mem_preimage, mem_closedBall, Real.dist_eq, sub_zero,
      e, Homeomorph.coe_mulLeft₀, abs_mul, abs_of_pos ha]
    exact mul_le_mul_iff_right₀ ha
  rw [← hpre]
  exact e.image_preimage _

lemma rootCanonicalFlow_rescales_time
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j) (t u : ℝ) (x : X (d + 1)) :
    rightAction (rightAction x (Matrix.SpecialLinearGroup.transvection hij u))
      (rootCanonicalFlow d j t) =
    rightAction (rightAction x (rootCanonicalFlow d j t))
      (Matrix.SpecialLinearGroup.transvection hij (Real.exp t * u)) := by
  let D := rootCanonicalFlow d j t
  have he : (rootCanonicalWeights d j i - rootCanonicalWeights d j j) * (-t) = t := by
    have hd := rootCanonicalWeights_difference d hij
    rw [show rootCanonicalWeights d j i - rootCanonicalWeights d j j = -1 by linarith]
    ring
  have hc : D⁻¹ * Matrix.SpecialLinearGroup.transvection hij u * D =
      Matrix.SpecialLinearGroup.transvection hij (Real.exp t * u) := by
    simpa only [D, rootCanonicalFlow, diagonalOneParameter_neg, neg_neg, he] using
      diagonal_conjugation_transvection (rootCanonicalWeights d j)
        (rootCanonicalWeights_sum d j) hij u (-t)
  rw [rightAction_mul, rightAction_mul]
  congr 1
  calc
    Matrix.SpecialLinearGroup.transvection hij u * D =
        D * (D⁻¹ * Matrix.SpecialLinearGroup.transvection hij u * D) := by group
    _ = _ := by rw [hc]

/-- A bad interval is sent to a bad interval of exponentially rescaled
radius for the image set under the canonical diagonal flow. -/
theorem intrinsic_bad_interval_scale
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (x : X (d + 1)) (t r : ℝ) (E : Set (X (d + 1))) (hE : MeasurableSet E)
    (heq : intrinsicRootLeaf hij μ (rightAction x (rootCanonicalFlow d j t)) =
      anchorNormalize ((intrinsicRootLeaf hij μ x).map
        (Homeomorph.mulLeft₀ (Real.exp t) (Real.exp_ne_zero t))) (ball 0 1))
    (c : ℝ≥0∞)
    (hbad : c * intrinsicRootLeaf hij μ x (closedBall 0 r) ≤
      intrinsicRootLeaf hij μ x
        ({u | rightAction x (Matrix.SpecialLinearGroup.transvection hij u) ∈ E} ∩
          closedBall 0 r)) :
    c * intrinsicRootLeaf hij μ (rightAction x (rootCanonicalFlow d j t))
        (closedBall 0 (Real.exp t * r)) ≤
      intrinsicRootLeaf hij μ (rightAction x (rootCanonicalFlow d j t))
        ({u | rightAction (rightAction x (rootCanonicalFlow d j t))
          (Matrix.SpecialLinearGroup.transvection hij u) ∈
            (rightActionHomeomorph (rootCanonicalFlow d j t)) '' E} ∩
          closedBall 0 (Real.exp t * r)) := by
  let e := Homeomorph.mulLeft₀ (Real.exp t) (Real.exp_ne_zero t)
  let f := rightActionHomeomorph (rootCanonicalFlow d j t)
  let S : Set ℝ := {u | rightAction x (Matrix.SpecialLinearGroup.transvection hij u) ∈ E}
  let T : Set ℝ := {u | rightAction (f x) (Matrix.SpecialLinearGroup.transvection hij u) ∈ f '' E}
  have hS : MeasurableSet S := hE.preimage (by
    exact ((continuous_rightAction_uncurry (d + 1)).comp
      (continuous_const.prodMk (continuous_rootTransvection hij))).measurable)
  have hpre : e ⁻¹' T = S := by
    ext u
    change (rightAction (rightAction x (rootCanonicalFlow d j t))
      (Matrix.SpecialLinearGroup.transvection hij (Real.exp t * u)) ∈ f '' E) ↔ _
    rw [← rootCanonicalFlow_rescales_time]
    exact f.injective.mem_set_image
  have himage : e '' S = T := by rw [← hpre]; exact e.image_preimage _
  have h := normalized_map_image_relative_bound (intrinsicRootLeaf hij μ x) e (ball 0 1)
    (closedBall 0 r) (S ∩ closedBall 0 r) isClosed_closedBall.measurableSet
    (hS.inter isClosed_closedBall.measurableSet) c hbad
  rw [image_inter e.injective, himage,
    scaling_image_closedBall_zero (Real.exp t) (Real.exp_pos t) r] at h
  dsimp only [T] at h
  rw [show f x = rightAction x (rootCanonicalFlow d j t) from rfl] at h
  simpa only [e, ← heq] using h

end DukePrimeDegree

end

end OAI
