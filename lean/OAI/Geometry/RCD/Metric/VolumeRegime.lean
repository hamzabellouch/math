import OAI.Geometry.RCD.Metric.ComparisonModel
import OAI.Geometry.RCD.Coordinates.RegularTangents

namespace OAI

/-!
# Volume convergence and the all-center volume regime

The volume-convergence hypothesis is the fixed-space rescaling
specialization of De Philippis--Gigli (2018), Theorems 1.2 and 1.3.
It concerns ball volumes in a Euclidean pointed limit. Bishop--Gromov
comparison and the density upper bound then control all smaller balls
around every nearby center.
-/

open Metric Set Filter MeasureTheory
open scoped Topology ENNReal

namespace RegularPointCoordinates

universe u

variable {X : Type u} [MetricSpace X] [MeasurableSpace X]

/-- Volume convergence for the normalized Hausdorff measure of
an `n`-dimensional noncollapsed RCD space. `omega` is the Euclidean unit-ball
volume. The source metric is unchanged: a rescaled radius `R` is `s i * R`
in the original metric. -/
def EuclideanRescalingVolumeConvergence (μ : Measure X) (n : ℕ) (p : X)
    (omega : ℝ) : Prop :=
  ∀ s : ℕ → ℝ, (∀ i, 0 < s i) → Tendsto s atTop (𝓝 0) →
    RescalingsConverge p (0 : Euclidean n) s → ∀ R : ℝ, 0 < R →
      Tendsto (fun i => μ.real (ball p (s i * R)) / s i ^ n)
        atTop (𝓝 (omega * R ^ n))

theorem regular_rescaling_volume_converges {μ : Measure X} {n : ℕ} {p : X}
    {omega : ℝ} (hcompact : PointedRescalingPrecompactness p)
    (hregular : IsRegular n p)
    (hvolume : EuclideanRescalingVolumeConvergence μ n p omega)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) (hszero : Tendsto s atTop (𝓝 0))
    {R : ℝ} (hR : 0 < R) :
    Tendsto (fun i => μ.real (ball p (s i * R)) / s i ^ n)
      atTop (𝓝 (omega * R ^ n)) :=
  hvolume s hs hszero (regular_rescalings_converge hcompact hregular s hs hszero) R hR

/-- The volume conclusion holds at every sufficiently small scale;
there is no preselected favorable sequence of scales. -/
theorem regular_small_scale_volume {μ : Measure X} {n : ℕ} {p : X}
    {omega : ℝ} (hcompact : PointedRescalingPrecompactness p)
    (hregular : IsRegular n p)
    (hvolume : EuclideanRescalingVolumeConvergence μ n p omega)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ r : ℝ, 0 < r → r < delta →
      |μ.real (ball p r) / r ^ n - omega| < epsilon := by
  by_contra hnot
  push Not at hnot
  have hchoice (i : ℕ) : ∃ r : ℝ, 0 < r ∧ r < 1 / ((i : ℝ) + 1) ∧
      epsilon ≤ |μ.real (ball p r) / r ^ n - omega| :=
    hnot (1 / ((i : ℝ) + 1)) (by positivity)
  choose s hspos hssmall hsbad using hchoice
  have hszero : Tendsto s atTop (𝓝 0) :=
    squeeze_zero (fun i => (hspos i).le) (fun i => (hssmall i).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have h := regular_rescaling_volume_converges hcompact hregular hvolume s hspos hszero
    (R := 1) zero_lt_one
  simp only [mul_one, one_pow] at h
  have hnear := (Metric.tendsto_atTop.mp h) epsilon hepsilon
  obtain ⟨i, hi⟩ := hnear
  have hi' : |μ.real (ball p (s i)) / s i ^ n - omega| < epsilon := by
    simpa only [Real.dist_eq] using hi i le_rfl
  exact (not_lt_of_ge (hsbad i)) hi'

/-- One large-ball lower bound and the density upper bound give
two-sided Euclidean volume bounds at every smaller radius and center.
All measures and distances here are in the original metric. -/
theorem uniform_volume_error_of_outer_ball
    {μ : Measure X} (m : ℕ) {a omega epsilon R D : ℝ} {p : X}
    (ha : 0 ≤ a) (homega : 0 < omega) (hepsilon1 : epsilon ≤ 1)
    (hRD : 0 < R + D)
    (hcomparison : BallVolumeComparison μ (comparisonModelVolume m a))
    (hdensity : ∀ y, SmallScaleVolumeUpper μ (comparisonModelVolume m a) y omega)
    (hfinite : ∀ y, μ (ball y (R + D)) ≠ ∞)
    (hlarge : ((1 - epsilon) * omega) * comparisonModelVolume m a (R + D) ≤
      μ.real (ball p R))
    (hmodel : Real.cosh (a * D) ^ m ≤ 1 + epsilon) :
    ∀ y, dist p y ≤ D → ∀ r, 0 < r → r ≤ D → r ≤ R + D →
      |μ.real (ball y r) / (omega * r ^ (m + 1)) - 1| ≤ epsilon := by
  intro y hy r hr hrD hrRD
  have hcoef : 0 ≤ (1 - epsilon) * omega := mul_nonneg (sub_nonneg.mpr hepsilon1) homega.le
  have hl := volume_lower_at_nearby_center hcomparison hy hr hrRD
    (comparisonModelVolume_pos m ha hr).le
    (comparisonModelVolume_pos m ha hRD) (hfinite y) hlarge
  have hl' : (1 - epsilon) * (omega * r ^ (m + 1)) ≤ μ.real (ball y r) := by
    calc
      _ = ((1 - epsilon) * omega) * r ^ (m + 1) := by ring
      _ ≤ ((1 - epsilon) * omega) * comparisonModelVolume m a r :=
        mul_le_mul_of_nonneg_left (comparisonModelVolume_bounds m ha hr.le).1 hcoef
      _ ≤ _ := hl
  have hu := volume_upper_of_small_scale_upper hcomparison
    (fun t ht => comparisonModelVolume_pos m ha ht) (hdensity y) hr
  have hsmall := comparisonModelVolume_relative_error m ha hr hrD
  have hmodelr : comparisonModelVolume m a r ≤ (1 + epsilon) * r ^ (m + 1) := by
    apply (div_le_iff₀ (pow_pos hr _)).mp
    linarith [hsmall.2]
  have hu' : μ.real (ball y r) ≤ (1 + epsilon) * (omega * r ^ (m + 1)) := by
    calc
      _ ≤ omega * comparisonModelVolume m a r := hu
      _ ≤ omega * ((1 + epsilon) * r ^ (m + 1)) :=
        mul_le_mul_of_nonneg_left hmodelr homega.le
      _ = _ := by ring
  rw [abs_le]
  have hden : 0 < omega * r ^ (m + 1) := mul_pos homega (pow_pos hr _)
  have hlq := (le_div_iff₀ hden).mpr hl'
  have huq := (div_le_iff₀ hden).mpr hu'
  constructor <;> linarith

/-- A regular point has a neighborhood on which every smaller ball has
almost Euclidean volume. This constructs a single neighborhood working
for all centers and all positive smaller radii simultaneously. -/
theorem exists_uniform_volume_neighborhood
    {μ : Measure X} (m : ℕ) {a omega epsilon rho : ℝ} {p : X}
    (ha : 0 ≤ a) (homega : 0 < omega) (hepsilon : 0 < epsilon)
    (hepsilon1 : epsilon ≤ 1) (hrho : 0 < rho)
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular (m + 1) p)
    (hvolume : EuclideanRescalingVolumeConvergence μ (m + 1) p omega)
    (hcomparison : BallVolumeComparison μ (comparisonModelVolume m a))
    (hdensity : ∀ y, SmallScaleVolumeUpper μ (comparisonModelVolume m a) y omega)
    (hfinite : ∀ y r, μ (ball y r) ≠ ∞) :
    ∃ D : ℝ, 0 < D ∧ D ≤ rho ∧ ∀ y, dist p y ≤ D →
      ∀ r, 0 < r → r ≤ D →
        |μ.real (ball y r) / (omega * r ^ (m + 1)) - 1| ≤ epsilon := by
  let s : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 1)
  have hs (i : ℕ) : 0 < s i := by dsimp [s]; positivity
  have hszero : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hv := regular_rescaling_volume_converges hcompact hregular hvolume s hs hszero
    (R := 1) zero_lt_one
  simp only [mul_one, one_pow] at hv
  have hm := comparisonModelVolume_density m ha hs hszero
  have hquot : Tendsto (fun i => μ.real (ball p (s i)) / comparisonModelVolume m a (s i))
      atTop (𝓝 omega) := by
    have ht := hv.div hm (by norm_num : (1 : ℝ) ≠ 0)
    simp only [div_one] at ht
    convert ht using 1
    funext i
    change μ.real (ball p (s i)) / comparisonModelVolume m a (s i) =
      (μ.real (ball p (s i)) / s i ^ (m + 1)) /
        (comparisonModelVolume m a (s i) / s i ^ (m + 1))
    field_simp [ne_of_gt (pow_pos (hs i) (m + 1)),
      ne_of_gt (comparisonModelVolume_pos m ha (hs i))]
  have hscale : Tendsto (fun i => a * s i) atTop (𝓝 0) := by
    simpa only [mul_zero] using hszero.const_mul a
  have hcosh : Tendsto (fun i => Real.cosh (a * s i) ^ m) atTop (𝓝 1) := by
    simpa using ((Real.continuous_cosh.tendsto 0).comp hscale).pow m
  have hless : (1 - epsilon) * omega < omega := by nlinarith
  obtain ⟨i, hi, hi'⟩ := ((hquot.eventually (lt_mem_nhds hless)).and
    (hcosh.eventually (gt_mem_nhds (by linarith : (1 : ℝ) < 1 + epsilon)))).exists
  let R := s i
  have hR : 0 < R := hs i
  have hlarge : ((1 - epsilon) * omega) * comparisonModelVolume m a R <
      μ.real (ball p R) :=
    (lt_div_iff₀ (comparisonModelVolume_pos m ha hR)).mp hi
  have hcont : ContinuousAt
      (fun D : ℝ => ((1 - epsilon) * omega) * comparisonModelVolume m a (R + D)) 0 :=
    (continuous_const.mul ((continuous_comparisonModelVolume m a).comp
      (continuous_const.add continuous_id))).continuousAt
  have hevent : ∀ᶠ D : ℝ in 𝓝 0,
      ((1 - epsilon) * omega) * comparisonModelVolume m a (R + D) <
        μ.real (ball p R) := by
    have hc : Tendsto
        (fun D : ℝ => ((1 - epsilon) * omega) * comparisonModelVolume m a (R + D))
        (𝓝 0) (𝓝 (((1 - epsilon) * omega) * comparisonModelVolume m a R)) := by
      simpa only [add_zero] using hcont.tendsto
    exact hc.eventually (gt_mem_nhds hlarge)
  obtain ⟨delta, hdelta, hnear⟩ := Metric.eventually_nhds_iff.mp hevent
  let D := min rho (min (R / 2) (delta / 2))
  have hD : 0 < D := lt_min hrho (lt_min (by linarith) (by linarith))
  have hDrho : D ≤ rho := min_le_left _ _
  have hDR : D ≤ R / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hDdelta : D ≤ delta / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hlargeD : ((1 - epsilon) * omega) * comparisonModelVolume m a (R + D) ≤
      μ.real (ball p R) := (hnear (by
        rw [Real.dist_eq, sub_zero, abs_of_pos hD]
        linarith)).le
  have hcoshD : Real.cosh (a * D) ^ m ≤ 1 + epsilon := by
    have hmon : Real.cosh (a * D) ≤ Real.cosh (a * R) := by
      apply Real.cosh_le_cosh.mpr
      rw [abs_of_nonneg (mul_nonneg ha hD.le), abs_of_nonneg (mul_nonneg ha hR.le)]
      exact mul_le_mul_of_nonneg_left (by linarith) ha
    exact (pow_le_pow_left₀ (Real.cosh_pos _).le hmon m).trans hi'.le
  refine ⟨D, hD, hDrho, ?_⟩
  intro y hy r hr hrD
  exact uniform_volume_error_of_outer_ball m ha homega hepsilon1 (by linarith)
    hcomparison hdensity (fun y => hfinite y (R + D)) hlargeD hcoshD
    y hy r hr hrD (by linarith)

end RegularPointCoordinates

end OAI
