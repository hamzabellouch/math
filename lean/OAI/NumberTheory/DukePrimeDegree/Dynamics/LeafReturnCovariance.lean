import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingAnnulus

namespace OAI

/-!
# Annular compact returns avoiding leafwise null exceptions

The simultaneous-return argument can also enforce any property holding
almost everywhere on the common leaf. In particular both rebasing laws
can be enforced, so equal initial leaves give equal terminal leaves at
the chosen compact return.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_annular_simultaneous_root_return_ae
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (K G : Set (X n)) (c a : ℝ≥0∞)
    (hgood : ∀ x ∈ G, ∀ r : ℝ, 0 < r →
      intrinsicRootLeaf hij μ x (rootHitTimes hij Kᶜ x ∩ Metric.closedBall 0 r) ≤
        c * intrinsicRootLeaf hij μ x (Metric.closedBall 0 r))
    (x y : X n) (hx : x ∈ G) (hy : y ∈ G)
    (heq : intrinsicRootLeaf hij μ x = intrinsicRootLeaf hij μ y)
    (r ρ : ℝ) (hr : 0 < r)
    (hpos : intrinsicRootLeaf hij μ x (Metric.closedBall 0 r) ≠ 0)
    (hfinite : intrinsicRootLeaf hij μ x (Metric.closedBall 0 r) ≠ ∞)
    (hsmall : intrinsicRootLeaf hij μ x (Metric.closedBall 0 (ρ * r)) ≤
      a * intrinsicRootLeaf hij μ x (Metric.closedBall 0 r))
    (hcoeff : c + c + a < 1)
    (P : ℝ → Prop) (hP : ∀ᵐ t ∂intrinsicRootLeaf hij μ x, P t) :
    ∃ t : ℝ, ρ * r < |t| ∧ |t| ≤ r ∧ P t ∧
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) ∈ K ∧
      rightAction y (Matrix.SpecialLinearGroup.transvection hij t) ∈ K := by
  let ν := intrinsicRootLeaf hij μ x
  let F := Metric.closedBall (0 : ℝ) (ρ * r) ∪ {t | ¬ P t}
  have hF : ν (Metric.closedBall (0 : ℝ) r ∩ F) ≤ ν (Metric.closedBall (0 : ℝ) (ρ * r)) := by
    calc
      _ ≤ ν F := measure_mono inter_subset_right
      _ ≤ ν (Metric.closedBall (0 : ℝ) (ρ * r)) + ν {t | ¬ P t} := measure_union_le _ _
      _ = _ := by rw [ae_iff.mp hP, add_zero]
  have hbudget : (c + c) * ν (Metric.closedBall 0 r) +
      ν (Metric.closedBall 0 r ∩ F) < ν (Metric.closedBall 0 r) := by
    calc
      _ ≤ (c + c) * ν (Metric.closedBall 0 r) + a * ν (Metric.closedBall 0 r) :=
        add_le_add le_rfl (hF.trans hsmall)
      _ = (c + c + a) * ν (Metric.closedBall 0 r) := (add_mul _ _ _).symm
      _ < 1 * ν (Metric.closedBall 0 r) := ENNReal.mul_lt_mul_left hpos hfinite hcoeff
      _ = _ := one_mul _
  obtain ⟨t, ht, hxK, hyK, hout⟩ := exists_simultaneous_root_return hij μ K G c hgood
    x y hx hy heq r hr F hbudget
  have hinner : t ∉ Metric.closedBall (0 : ℝ) (ρ * r) := fun h => hout (Or.inl h)
  have hp : P t := by
    by_contra h
    exact hout (Or.inr h)
  exact ⟨t, by simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] using hinner,
    by simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using ht, hp, hxK, hyK⟩

theorem exists_annular_return_with_equal_leaves
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (K G : Set (X n)) (c a : ℝ≥0∞)
    (hgood : ∀ x ∈ G, ∀ r : ℝ, 0 < r →
      intrinsicRootLeaf hij μ x (rootHitTimes hij Kᶜ x ∩ Metric.closedBall 0 r) ≤
        c * intrinsicRootLeaf hij μ x (Metric.closedBall 0 r))
    (x y : X n) (hx : x ∈ G) (hy : y ∈ G)
    (heq : intrinsicRootLeaf hij μ x = intrinsicRootLeaf hij μ y)
    (hrebasex : ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
      intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
        basedRealMeasure (intrinsicRootLeaf hij μ x) t)
    (hrebasey : ∀ᵐ t ∂intrinsicRootLeaf hij μ y,
      intrinsicRootLeaf hij μ (rightAction y (Matrix.SpecialLinearGroup.transvection hij t)) =
        basedRealMeasure (intrinsicRootLeaf hij μ y) t)
    (r ρ : ℝ) (hr : 0 < r)
    (hpos : intrinsicRootLeaf hij μ x (Metric.closedBall 0 r) ≠ 0)
    (hfinite : intrinsicRootLeaf hij μ x (Metric.closedBall 0 r) ≠ ∞)
    (hsmall : intrinsicRootLeaf hij μ x (Metric.closedBall 0 (ρ * r)) ≤
      a * intrinsicRootLeaf hij μ x (Metric.closedBall 0 r))
    (hcoeff : c + c + a < 1) :
    ∃ t : ℝ, ρ * r < |t| ∧ |t| ≤ r ∧
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) ∈ K ∧
      rightAction y (Matrix.SpecialLinearGroup.transvection hij t) ∈ K ∧
      intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
        intrinsicRootLeaf hij μ (rightAction y (Matrix.SpecialLinearGroup.transvection hij t)) := by
  rw [← heq] at hrebasey
  obtain ⟨t, hlo, hhi, he, hxK, hyK⟩ := exists_annular_simultaneous_root_return_ae
    hij μ K G c a hgood x y hx hy heq r ρ hr hpos hfinite hsmall hcoeff
    (fun t => intrinsicRootLeaf hij μ
      (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
        intrinsicRootLeaf hij μ (rightAction y (Matrix.SpecialLinearGroup.transvection hij t)))
    (by
      filter_upwards [hrebasex, hrebasey] with t hx hy
      exact hx.trans hy.symm)
  exact ⟨t, hlo, hhi, hxK, hyK, he⟩

end DukePrimeDegree

end

end OAI
