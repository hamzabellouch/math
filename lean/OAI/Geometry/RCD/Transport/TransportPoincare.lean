import OAI.Geometry.RCD.Sobolev.LocalMedian
import OAI.Geometry.RCD.Transport.TransportLevelBound
import OAI.Geometry.RCD.Metric.LowerCurvatureVolume
import OAI.Geometry.RCD.Sobolev.MeanPoincareInput

namespace OAI

/-! # The local L² Poincare estimate from RCD transport

The two median level sets are transported to their larger opposite sets.
The normalization cancels from the compression bound and only energy in
the eightfold ball remains.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

private theorem measure_sdiff_le_inter_of_half {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {Ω T : Set X} (ht : MeasurableSet T) (hΩt : μ Ω ≠ ∞)
    (hhalf : μ.real Ω / 2 ≤ μ.real (Ω ∩ T)) : μ (Ω \ T) ≤ μ (Ω ∩ T) := by
  have hAt : μ (Ω \ T) ≠ ∞ := ne_top_of_le_ne_top hΩt (measure_mono sdiff_subset)
  have hBt : μ (Ω ∩ T) ≠ ∞ := ne_top_of_le_ne_top hΩt (measure_mono inter_subset_left)
  apply (ENNReal.toReal_le_toReal hAt hBt).mp
  have heq := measureReal_inter_add_sdiff (μ := μ) (s := Ω) ht hΩt
  change μ.real (Ω \ T) ≤ μ.real (Ω ∩ T)
  linarith

private theorem split_level_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {Ω : Set X} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (μ.restrict Ω)]
    (u : Lp ℝ 2 μ) (k : ℝ) :
    (∫ x in Ω, (u x - k) ^ 2 ∂μ) =
      (∫ x in Ω \ {x | u x ≤ k}, (u x - k) ^ 2 ∂μ) +
      (∫ x in Ω \ {x | k ≤ u x}, (u x - k) ^ 2 ∂μ) := by
  have hu : Measurable (u : X → ℝ) := Lp.stronglyMeasurable u |>.measurable
  have hT := measurableSet_le hu (measurable_const (a := k))
  have hS := measurableSet_le (measurable_const (a := k)) hu
  let F : X → ℝ := Ω.indicator (fun x => (u x - k) ^ 2)
  have hvar : Integrable (fun x => (u x - k) ^ 2) (μ.restrict Ω) :=
    (((Lp.memLp u).mono_measure Measure.restrict_le_self).sub (memLp_const k)).integrable_sq
  have hFi : Integrable F μ := (integrable_indicator_iff hΩ).mpr hvar
  have heq : F = (Ω \ {x | u x ≤ k}).indicator F + (Ω \ {x | k ≤ u x}).indicator F := by
    funext x
    by_cases hx : x ∈ Ω
    · rcases lt_trichotomy (u x) k with h | h | h
      · simp [F, hx, h.le, h.not_ge]
      · simp [F, hx, h]
      · simp [F, hx, h.le, h.not_ge]
    · simp [F, hx]
  have hA : MeasurableSet (Ω \ {x | u x ≤ k}) := hΩ.diff hT
  have hB : MeasurableSet (Ω \ {x | k ≤ u x}) := hΩ.diff hS
  calc
    _ = ∫ x, F x ∂μ := (integral_indicator hΩ).symm
    _ = (∫ x in Ω \ {x | u x ≤ k}, F x ∂μ) +
        ∫ x in Ω \ {x | k ≤ u x}, F x ∂μ := by
      conv_lhs => rw [heq]
      simp only [Pi.add_apply]
      rw [integral_add (hFi.indicator hA) (hFi.indicator hB),
        integral_indicator hA, integral_indicator hB]
    _ = _ := by
      congr 1
      · apply setIntegral_congr_fun hA
        intro x hx
        exact indicator_of_mem hx.1 _
      · apply setIntegral_congr_fun hB
        intro x hx
        exact indicator_of_mem hx.1 _

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The direct transport estimate before replacing its curvature factor
by a constant depending only on the rescaled lower curvature bound. -/
theorem NoncollapsedRCD.local_mean_poincare_transport
    {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (p : X) {R : ℝ} (hR : 0 < R)
    {u G : Lp ℝ 2 (hausdorff n X)} (hG : IsRelaxedSlope (hausdorff n X) u G) :
    ∃ k : ℝ, (∫ x in ball p R, (u x - k) ^ 2 ∂hausdorff n X) ≤
      2 * ((2 * R) ^ 2 * Real.exp ((n : ℝ) * (4 * R) * Real.sqrt (|K| / (n - 1))) *
        (∫ x in ball p (8 * R), (G x) ^ 2 ∂hausdorff n X)) := by
  let μ := hausdorff n X
  let Ω := ball p R
  have hΩt : μ Ω ≠ ∞ := (hX.finiteOnBounded Ω isBounded_ball).ne
  have hΩ0 : μ Ω ≠ 0 := (hX.fullSupport p R hR).ne'
  let : IsFiniteMeasure (μ.restrict Ω) := ⟨by simpa using hΩt.lt_top⟩
  have hu : Measurable (u : X → ℝ) := Lp.stronglyMeasurable u |>.measurable
  obtain ⟨k, hk₀, hk₁⟩ := exists_local_median μ measurableSet_ball hΩ0 hΩt u hu
  have hT := measurableSet_le hu (measurable_const (a := k))
  have hS := measurableSet_le (measurable_const (a := k)) hu
  have hsplit := split_level_integral μ (Ω := Ω) measurableSet_ball u k
  have hup := hX.balanced_level_integral_bound hn p hR (measurableSet_ball.diff hT)
    (measurableSet_ball.inter hT)
    (sdiff_subset.trans ball_subset_closedBall) (inter_subset_left.trans ball_subset_closedBall)
    (measure_sdiff_le_inter_of_half μ hT hΩt hk₀) hG k ?_
  · have hlo := hX.balanced_level_integral_bound hn p hR (measurableSet_ball.diff hS)
      (measurableSet_ball.inter hS)
      (sdiff_subset.trans ball_subset_closedBall) (inter_subset_left.trans ball_subset_closedBall)
      (measure_sdiff_le_inter_of_half μ hS hΩt hk₁) hG k ?_
    · refine ⟨k, ?_⟩
      rw [hsplit]
      linarith
    · intro x hx y hy
      have hx' : u x < k := lt_of_not_ge hx.2
      have hy' : k ≤ u y := hy.2
      nlinarith [mul_nonneg (sub_nonneg.mpr hx'.le) (sub_nonneg.mpr hy')]
  · intro x hx y hy
    have hx' : k < u x := lt_of_not_ge hx.2
    have hy' : u y ≤ k := hy.2
    nlinarith [mul_nonneg (sub_nonneg.mpr hx'.le) (sub_nonneg.mpr hy')]

/-- The local Poincare bound obtained from bounded-compression RCD transport. -/
theorem NoncollapsedRCD.localMeanPoincareInput {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [ProperSpace X] (hn : 2 ≤ n) :
    LocalMeanPoincareInput hX := by
  let μ := hausdorff n X
  let K' := min K 0
  have hY : NoncollapsedRCD K' n X := by
    by_cases hK : K ≤ 0
    · simpa only [K', min_eq_left hK] using hX
    · simpa only [K', min_eq_right (le_of_not_ge hK)] using
        hX.zero_of_nonneg_curvature hn (le_of_not_ge hK)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  intro κ hκ
  let D := Real.exp (4 * (n : ℝ) * Real.sqrt (κ / (n - 1)))
  have hD : 1 ≤ D := Real.one_le_exp_iff.mpr (by positivity)
  refine ⟨4 * D, by linarith, ?_⟩
  intro p R hR hKR w
  let u := SobolevSpace.toLp μ hX.quadratic w
  let G := SobolevSpace.minimalSlope μ hX.quadratic w
  obtain ⟨k, hk⟩ := hY.local_mean_poincare_transport hn p hR
    (SobolevSpace.minimalSlope_isRelaxed μ hX.quadratic w)
  have hcurv : |K'| * R ^ 2 ≤ κ := by
    by_cases hK : K ≤ 0
    · simp only [K', min_eq_left hK, abs_of_nonpos hK]
      nlinarith
    · simpa only [K', min_eq_right (le_of_not_ge hK), abs_zero, zero_mul] using hκ
  have hroot : R * Real.sqrt (|K'| / (n - 1)) ≤ Real.sqrt (κ / (n - 1)) := by
    have hs : (R * Real.sqrt (|K'| / (n - 1))) ^ 2 ≤ κ / (n - 1) := by
      calc
        _ = |K'| * R ^ 2 / (n - 1) := by
          rw [mul_pow, Real.sq_sqrt (div_nonneg (abs_nonneg _) hn1.le)]
          ring
        _ ≤ _ := div_le_div_of_nonneg_right hcurv hn1.le
    have hsq := Real.sq_sqrt (div_nonneg hκ hn1.le)
    nlinarith [mul_nonneg hR.le (Real.sqrt_nonneg (|K'| / (n - 1))),
      Real.sqrt_nonneg (κ / (n - 1))]
  have hexp : Real.exp ((n : ℝ) * (4 * R) * Real.sqrt (|K'| / (n - 1))) ≤ D := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ 4 * (n : ℝ))
    nlinarith only [this]
  have henergy : (∫ x in ball p (8 * R), localGamma μ hX.quadratic w w x ∂μ) =
      ∫ x in ball p (8 * R), G x ^ 2 ∂μ :=
    integral_congr_ae (ae_restrict_of_ae (localGamma_self μ hX.quadratic w))
  refine ⟨k, ?_⟩
  change (∫ x in ball p R, (u x - k) ^ 2 ∂μ) ≤
    (4 * D * R) ^ 2 * ∫ x in ball p (8 * R), localGamma μ hX.quadratic w w x ∂μ
  rw [henergy]
  have hJ : 0 ≤ ∫ x in ball p (8 * R), G x ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hcoeff : 8 * D ≤ (4 * D) ^ 2 := by nlinarith
  calc
    _ ≤ 2 * ((2 * R) ^ 2 * Real.exp ((n : ℝ) * (4 * R) *
        Real.sqrt (|K'| / (n - 1))) * (∫ x in ball p (8 * R), G x ^ 2 ∂μ)) := hk
    _ ≤ 2 * ((2 * R) ^ 2 * D * (∫ x in ball p (8 * R), G x ^ 2 ∂μ)) := by gcongr
    _ = (8 * D * R ^ 2) * (∫ x in ball p (8 * R), G x ^ 2 ∂μ) := by ring
    _ ≤ ((4 * D) ^ 2 * R ^ 2) * (∫ x in ball p (8 * R), G x ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg R)) hJ
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI
