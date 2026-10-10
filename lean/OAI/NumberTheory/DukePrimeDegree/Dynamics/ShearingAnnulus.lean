import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafClosedRadius
import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafPairSelection

namespace OAI

/-!
# Annular simultaneous returns

Small mass near the root origin excludes the central portion of a
shearing interval. The relative maximal bound then supplies simultaneous
compact returns in the remaining annulus, as in EKL Section 4.5.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma scaling_preimage_closedBall (s r : ℝ) (hs : 0 < s) :
    (Homeomorph.mulLeft₀ s hs.ne') ⁻¹' closedBall 0 r = closedBall 0 (r / s) := by
  ext t
  simp only [mem_preimage, mem_closedBall, Real.dist_eq, sub_zero,
    Homeomorph.coe_mulLeft₀, abs_mul, abs_of_pos hs]
  rw [le_div_iff₀ hs, mul_comm]

lemma normalized_scaling_closedBall (ν : Measure ℝ) (s r : ℝ) (hs : 0 < s) :
    anchorNormalize (ν.map (Homeomorph.mulLeft₀ s hs.ne')) (ball 0 1)
      (closedBall 0 r) = (ν (ball 0 (1 / s)))⁻¹ * ν (closedBall 0 (r / s)) := by
  change (ν.map (Homeomorph.mulLeft₀ s hs.ne') (ball 0 1))⁻¹ *
    ν.map (Homeomorph.mulLeft₀ s hs.ne') (closedBall 0 r) = _
  rw [Measure.map_apply (Homeomorph.mulLeft₀ s hs.ne').measurable isOpen_ball.measurableSet,
    Measure.map_apply (Homeomorph.mulLeft₀ s hs.ne').measurable isClosed_closedBall.measurableSet,
    realScaling_preimage_ball s 1 hs, scaling_preimage_closedBall s r hs]

theorem normalized_small_ball_gives_annulus
    (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (s ρ : ℝ) (hs : 0 < s)
    (hpos : ν (ball 0 (1 / s)) ≠ 0) (a : ℝ≥0∞)
    (hsmall : anchorNormalize (ν.map (Homeomorph.mulLeft₀ s hs.ne')) (ball 0 1)
      (closedBall 0 ρ) < a) :
    ν (closedBall 0 (ρ / s)) < a * ν (closedBall 0 (1 / s)) := by
  rw [normalized_scaling_closedBall ν s ρ hs] at hsmall
  have hfinite : ν (ball 0 (1 / s)) ≠ ∞ := measure_ball_lt_top.ne
  have h := ENNReal.mul_lt_mul_left hpos hfinite hsmall
  rw [mul_right_comm (ν (ball 0 (1 / s)))⁻¹, ENNReal.inv_mul_cancel hpos hfinite, one_mul] at h
  exact h.trans_le (mul_le_mul' le_rfl (measure_mono ball_subset_closedBall))

theorem exists_annular_simultaneous_root_return
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (K G : Set (X n)) (c a : ℝ≥0∞)
    (hgood : ∀ x ∈ G, ∀ r : ℝ, 0 < r →
      intrinsicRootLeaf hij μ x (rootHitTimes hij Kᶜ x ∩ closedBall 0 r) ≤
        c * intrinsicRootLeaf hij μ x (closedBall 0 r))
    (x y : X n) (hx : x ∈ G) (hy : y ∈ G)
    (heq : intrinsicRootLeaf hij μ x = intrinsicRootLeaf hij μ y)
    (r ρ : ℝ) (hr : 0 < r)
    (hpos : intrinsicRootLeaf hij μ x (closedBall 0 r) ≠ 0)
    (hfinite : intrinsicRootLeaf hij μ x (closedBall 0 r) ≠ ∞)
    (hsmall : intrinsicRootLeaf hij μ x (closedBall 0 (ρ * r)) ≤
      a * intrinsicRootLeaf hij μ x (closedBall 0 r))
    (hcoeff : c + c + a < 1) :
    ∃ t : ℝ, ρ * r < |t| ∧ |t| ≤ r ∧
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) ∈ K ∧
      rightAction y (Matrix.SpecialLinearGroup.transvection hij t) ∈ K := by
  let M := intrinsicRootLeaf hij μ x (closedBall 0 r)
  have hbudget : (c + c) * M +
      intrinsicRootLeaf hij μ x (closedBall 0 r ∩ closedBall 0 (ρ * r)) < M := by
    calc
      _ ≤ (c + c) * M + a * M := add_le_add le_rfl
        ((measure_mono inter_subset_right).trans hsmall)
      _ = (c + c + a) * M := (add_mul _ _ _).symm
      _ < 1 * M := ENNReal.mul_lt_mul_left hpos hfinite hcoeff
      _ = M := one_mul M
  obtain ⟨t, ht, hxK, hyK, hout⟩ := exists_simultaneous_root_return hij μ K G c hgood
    x y hx hy heq r hr (closedBall 0 (ρ * r)) hbudget
  refine ⟨t, ?_, ?_, hxK, hyK⟩
  · simpa only [mem_closedBall, Real.dist_eq, sub_zero, not_le] using hout
  · simpa only [mem_closedBall, Real.dist_eq, sub_zero] using ht

end DukePrimeDegree

end

end OAI
