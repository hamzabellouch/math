import OAI.Geometry.RCD.Metric.MetricInnerLawSubsequence
import OAI.Geometry.RCD.Sobolev.WeakCompactUniformTests
import OAI.Geometry.RCD.Metric.ApproximationRestriction

namespace OAI

/-! # Uniform measured tests for the prescribed metric approximations -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem euclideanBallProbability_supported {n : ℕ} {S R : ℝ} (hS : 0 < S) (hSR : S ≤ R) :
    ∀ᵐ z ∂(euclideanBallProbability n S : Measure (Euclidean n)), z ∈ closedBall 0 R := by
  let : IsFiniteMeasure (volume.restrict (ball (0 : Euclidean n) S)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top (μ := (volume : Measure (Euclidean n))) (x := 0) (r := S))⟩
  have hn : volume.restrict (ball (0 : Euclidean n) S) ≠ 0 := by
    intro h
    have hh := congrArg (fun μ : Measure (Euclidean n) => μ univ) h
    simp only [Measure.restrict_apply_univ,Measure.coe_zero,Pi.zero_apply] at hh
    exact (measure_ball_pos volume 0 hS).ne' hh
  change ∀ᵐ z ∂(normalizedProbabilityLaw (volume.restrict (ball (0 : Euclidean n) S)) :
    Measure (Euclidean n)), z ∈ closedBall 0 R
  filter_upwards [normalized_restriction_ae_mem volume measurableSet_ball hn] with z hz
  exact ball_subset_closedBall (hz.trans_le hSR)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.uniform_metric_measure_tests {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hK : K ≤ 0)
    (S η : ℝ) (hS : 0 < S) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : X) (r : ℝ), 0 < r → -δ ≤ K*r^2 →
      ∀ V : X → Euclidean n, Measurable V → IsPointedApproximation p 0 r (2*S) δ V →
      ∀ φ : Euclidean n → ℝ, LipschitzWith 1 φ → (∀ z, |φ z| ≤ 1) →
        |((hausdorff n X).real (ball p (S*r)))⁻¹ * (∫ x in ball p (S*r), φ (V x) ∂hausdorff n X) -
          (volume.real (ball (0 : Euclidean n) S))⁻¹ * (∫ z in ball 0 S, φ z)| ≤ η := by
  classical
  by_contra hnot
  push Not at hnot
  let b := min 1 (1/((2*S)^2+1))
  have hb : 0 < b := lt_min zero_lt_one (by positivity)
  let ε := fun k : ℕ => min b (1/((k:ℝ)+1))
  have hεpos (k : ℕ) : 0 < ε k := lt_min hb (by positivity)
  have hε1 (k : ℕ) : ε k ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hεB (k : ℕ) : ε k ≤ 1/((2*S)^2+1) := (min_le_left _ _).trans (min_le_right _ _)
  have hεlim : Tendsto ε atTop (𝓝 0) := squeeze_zero (fun k => (hεpos k).le)
    (fun _ => min_le_right _ _) tendsto_one_div_add_atTop_nhds_zero_nat
  have hex (k : ℕ) := hnot (ε k) (hεpos k)
  choose p r hr hcurv V hVm hV φ hφLip hφbound hbad using hex
  have hlarge (k : ℕ) : -1 ≤ K*((2*S)*r k)^2 := by
    have he := (le_div_iff₀ (show 0 < (2*S)^2+1 by positivity)).mp (hεB k)
    have hm := mul_nonneg (sq_nonneg (2*S)) (show 0 ≤ K*(r k)^2+ε k by linarith [hcurv k])
    nlinarith [hεpos k]
  obtain ⟨α,hα,hlim⟩ := hX.metric_inner_law_subsequence hn hK hS
    (show S < 2*S by linarith) p r ε V hr hεlim hε1 hcurv hlarge hVm hV
  let P := fun k => normalizedBallPushforward (hausdorff n X)
    (p (α k)) (r (α k)) S (V (α k)) (hX.finiteOnBounded _ isBounded_ball).ne
  have hpos (k : ℕ) : 0 < (hausdorff n X).real (ball (p k) (S*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  have hsupport (k : ℕ) : ∀ᵐ z ∂(P k : Measure (Euclidean n)), z ∈ closedBall 0 (S+6) := by
    have hvsmall := (hV (α k)).restrict_radius (hr (α k)) hS.le (by linarith : S ≤ 2*S)
      (hεpos (α k)).le
    filter_upwards [normalizedBallPushforward_supported (hausdorff n X) (p (α k))
      (hr (α k)) hS.le (V (α k)) (hVm (α k)) hvsmall
      (hX.finiteOnBounded _ isBounded_ball).ne (hpos (α k))] with z hz
    exact closedBall_subset_closedBall (by linarith [hε1 (α k)]) hz
  have hu := weak_compact_uniform_tests hlim (isCompact_closedBall (0 : Euclidean n) (S+6))
    hsupport (euclideanBallProbability_supported hS (by linarith : S ≤ S+6)) hη
  obtain ⟨k,hk⟩ := hu.exists
  have htest := hk (φ (α k)) (hφLip (α k)) (hφbound (α k))
  rw [normalizedBallPushforward_integral _ _ _ _ _ _ (hpos (α k)) (hVm (α k))
    (hφLip (α k)).continuous,euclideanBallProbability_integral hS] at htest
  exact (hbad (α k)).not_ge htest

end RegularPointCoordinates

end

end OAI
