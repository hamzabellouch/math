import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPairTimeSelection

namespace OAI

/-!
# Comparing leaves at two selected diagonal times

Normalized scaling composes exactly when the leaf gives positive mass
to every neighborhood of the origin. This transfers the small-ball
bound at the second recurrence time to the annulus at the first time,
the measure comparison in EKL Lemma 4.5.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem normalized_scaling_comp (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r))
    (c e : ℝ) (hc : 0 < c) :
    anchorNormalize
      ((anchorNormalize (ν.map (fun u => c * u)) (Metric.ball 0 1)).map (fun u => e * u))
      (Metric.ball 0 1) =
    anchorNormalize (ν.map (fun u => (e * c) * u)) (Metric.ball 0 1) := by
  have hm : ν.map (fun u => c * u) (Metric.ball 0 1) = ν (Metric.ball 0 (1 / c)) := by
    rw [Measure.map_apply (show Measurable (fun u : ℝ => c * u) from by fun_prop)
      Metric.isOpen_ball.measurableSet]
    exact congrArg ν (realScaling_preimage_ball c 1 hc)
  change anchorNormalize (((ν.map (fun u => c * u) (Metric.ball 0 1))⁻¹ •
    ν.map (fun u => c * u)).map (fun u => e * u)) (Metric.ball 0 1) = _
  rw [Measure.map_smul _ (show AEMeasurable (fun u : ℝ => e * u)
    (ν.map (fun u => c * u)) from (by fun_prop : Measurable (fun u : ℝ => e * u)).aemeasurable)]
  rw [anchorNormalize_smul _ _ _ (by rw [hm]; exact ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne)
    (by rw [hm]; exact ENNReal.inv_ne_top.mpr (hp _ (by positivity)).ne')]
  rw [Measure.map_map (show Measurable (fun u : ℝ => e * u) from by fun_prop)
    (show Measurable (fun u : ℝ => c * u) from by fun_prop)]
  congr 2
  funext u
  exact (mul_assoc e c u).symm

theorem normalized_scaling_ball_pos (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r))
    (c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    0 < anchorNormalize (ν.map (fun u => c * u)) (Metric.ball 0 1) (Metric.ball 0 r) := by
  change 0 < anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc.ne'))
    (Metric.ball 0 1) (Metric.ball 0 r)
  rw [normalized_realScaling_ball ν c r hc]
  exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne)
    (hp _ (div_pos hr hc)).ne'

theorem rootPair_leaf_covariance_between_times
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ a : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij a) = x → a = 0)
    (z : X n) (τ v : ℝ)
    (hp : ∀ r : ℝ, 0 < r → 0 < intrinsicRootKernel hij μ hfree z (Metric.ball 0 r))
    (hτ : RootPairLeafCovariance hij μ hfree z τ)
    (hv : RootPairLeafCovariance hij μ hfree z v) :
    intrinsicRootKernel hij μ hfree (rightAction z (rootPairFlow i j (-v))) =
      anchorNormalize ((intrinsicRootKernel hij μ hfree
        (rightAction z (rootPairFlow i j (-τ)))).map
          (fun u => Real.exp (-2 * (v - τ)) * u)) (Metric.ball 0 1) := by
  change intrinsicRootKernel hij μ hfree (rightAction z (rootPairFlow i j (-τ))) =
    anchorNormalize ((intrinsicRootKernel hij μ hfree z).map
      (fun u => Real.exp (-2 * τ) * u)) (Metric.ball 0 1) at hτ
  change intrinsicRootKernel hij μ hfree (rightAction z (rootPairFlow i j (-v))) =
    anchorNormalize ((intrinsicRootKernel hij μ hfree z).map
      (fun u => Real.exp (-2 * v) * u)) (Metric.ball 0 1) at hv
  rw [hv, hτ, normalized_scaling_comp _ hp _ _ (Real.exp_pos _)]
  congr 2
  funext u
  rw [← Real.exp_add]
  congr 2
  ring

theorem rootPair_small_ball_gives_annulus
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ a : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij a) = x → a = 0)
    (z : X n) (τ v ρ : ℝ) (a : ℝ≥0∞)
    (hp : ∀ r : ℝ, 0 < r → 0 < intrinsicRootKernel hij μ hfree z (Metric.ball 0 r))
    (hτ : RootPairLeafCovariance hij μ hfree z τ)
    (hv : RootPairLeafCovariance hij μ hfree z v)
    (hsmall : intrinsicRootKernel hij μ hfree
      (rightAction z (rootPairFlow i j (-v))) (Metric.closedBall 0 ρ) < a) :
    intrinsicRootKernel hij μ hfree (rightAction z (rootPairFlow i j (-τ)))
        (Metric.closedBall 0 (ρ * Real.exp (2 * (v - τ)))) <
      a * intrinsicRootKernel hij μ hfree (rightAction z (rootPairFlow i j (-τ)))
        (Metric.closedBall 0 (Real.exp (2 * (v - τ)))) := by
  let ν := intrinsicRootKernel hij μ hfree (rightAction z (rootPairFlow i j (-τ)))
  have hνpos : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r) := by
    change intrinsicRootKernel hij μ hfree (rightAction z (rootPairFlow i j (-τ))) =
      anchorNormalize ((intrinsicRootKernel hij μ hfree z).map
        (fun u => Real.exp (-2 * τ) * u)) (Metric.ball 0 1) at hτ
    intro r hr
    dsimp only [ν]
    rw [hτ]
    exact normalized_scaling_ball_pos _ hp _ r (Real.exp_pos _) hr
  have he := rootPair_leaf_covariance_between_times hij μ hfree z τ v hp hτ hv
  rw [he] at hsmall
  have h := normalized_small_ball_gives_annulus ν (Real.exp (-2 * (v - τ))) ρ
    (Real.exp_pos _) (hνpos _ (by positivity)).ne' a hsmall
  have hinv : (Real.exp (-2 * (v - τ)))⁻¹ = Real.exp (2 * (v - τ)) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  simpa only [div_eq_mul_inv, hinv, one_mul] using h

end DukePrimeDegree

end

end OAI
