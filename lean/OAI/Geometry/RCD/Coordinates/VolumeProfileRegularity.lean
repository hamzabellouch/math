import OAI.Geometry.RCD.Metric.ComparisonModel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

namespace OAI

/-!
# Absolute continuity of the Euclidean-normalized volume profile

Bishop--Gromov and a positive Lipschitz comparison model make ball volume
Lipschitz on every compact interval of positive radii. Multiplication by the
smooth Euclidean normalization then gives the absolute continuity needed by
the radial source budget.
-/

open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace RegularPointCoordinates

theorem volume_profile_lipschitzOn {V model : ℝ → ℝ} {a b m0 V0 : ℝ}
    (hm0 : 0 < m0) (hV0 : 0 ≤ V0) (K : ℝ≥0)
    (hVmono : MonotoneOn V (Icc a b)) (hVnonneg : ∀ t ∈ Icc a b, 0 ≤ V t)
    (hVupper : ∀ t ∈ Icc a b, V t ≤ V0)
    (hmodel : ∀ t ∈ Icc a b, m0 ≤ model t)
    (hLip : LipschitzOnWith K model (Icc a b))
    (hcross : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → V t * model s ≤ V s * model t) :
    LipschitzOnWith ⟨V0 * K / m0, by positivity⟩ V (Icc a b) := by
  let C : ℝ≥0 := ⟨V0 * K / m0, by positivity⟩
  have hdelta (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) (hst : s ≤ t) :
      V t - V s ≤ C * (t - s) := by
    have hinc : 0 ≤ V t - V s := sub_nonneg.mpr (hVmono hs ht hst)
    have hml := hLip.dist_le_mul t ht s hs
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hst)] at hml
    have hb : (V t - V s) * m0 ≤ V0 * K * (t - s) := by
      calc
        _ ≤ (V t - V s) * model s := mul_le_mul_of_nonneg_left (hmodel s hs) hinc
        _ ≤ V s * (model t - model s) := by nlinarith [hcross s hs t ht hst]
        _ ≤ V s * |model t - model s| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (hVnonneg s hs)
        _ ≤ V s * (K * (t - s)) := mul_le_mul_of_nonneg_left hml (hVnonneg s hs)
        _ ≤ V0 * K * (t - s) := by
          have hh := mul_le_mul_of_nonneg_right (hVupper s hs)
            (mul_nonneg K.coe_nonneg (sub_nonneg.mpr hst))
          simpa only [mul_assoc] using hh
    have hd := (le_div_iff₀ hm0).mpr hb
    exact hd.trans_eq (by
      change V0 * (K : ℝ) * (t - s) / m0 = (V0 * (K : ℝ) / m0) * (t - s)
      ring)
  have hordered (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) (hst : s ≤ t) :
      dist (V s) (V t) ≤ C * dist s t := by
    have hv := hVmono hs ht hst
    simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hv),
      abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using hdelta s hs t ht hst
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rcases le_total s t with hst | hts
  · exact hordered s hs t ht hst
  · simpa only [dist_comm] using hordered t ht s hs hts

/-- The fixed negative-curvature comparison volume is continuously differentiable. -/
theorem contDiff_one_comparisonModelVolume (m : ℕ) (c : ℝ) :
    ContDiff ℝ 1 (comparisonModelVolume m c) := by
  have hcont : Continuous (fun t => radialComparison c t ^ m) :=
    (continuous_radialComparison c).pow m
  have hd (r : ℝ) : HasDerivAt (comparisonModelVolume m c)
      ((m + 1 : ℝ) * radialComparison c r ^ m) r := by
    change HasDerivAt (fun r => (m + 1 : ℝ) * ∫ t in 0..r, radialComparison c t ^ m) _ r
    exact (intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 r)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt).const_mul _
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun r => (hd r).differentiableAt, ?_⟩
  have he : deriv (comparisonModelVolume m c) = fun r => (m + 1 : ℝ) * radialComparison c r ^ m :=
    funext fun r => (hd r).deriv
  rw [he]
  exact continuous_const.mul hcont

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- Ball volume is absolutely continuous away from radius zero under the
published Bishop--Gromov comparison with the explicit model. -/
theorem ball_volume_absolutelyContinuous {μ : Measure X} (m : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hBG : BallVolumeComparison μ (comparisonModelVolume m c)) (x : X)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hfin : μ (ball x b) ≠ ∞) :
    AbsolutelyContinuousOnInterval (fun t => μ.real (ball x t)) a b := by
  have hb : 0 < b := ha.trans_le hab
  let model := comparisonModelVolume m c
  obtain ⟨K, hK⟩ := (contDiff_one_comparisonModelVolume m c).contDiffOn.exists_lipschitzOnWith
    (s := Icc a b) (by decide) (convex_Icc a b) isCompact_Icc
  have hmono : MonotoneOn (fun t => μ.real (ball x t)) (Icc a b) := by
    intro s hs t ht hst
    exact measureReal_mono (ball_subset_ball hst)
      (measure_ne_top_of_subset (ball_subset_ball ht.2) hfin)
  have hupper (t : ℝ) (ht : t ∈ Icc a b) : μ.real (ball x t) ≤ μ.real (ball x b) :=
    measureReal_mono (ball_subset_ball ht.2) hfin
  have hmodel (t : ℝ) (ht : t ∈ Icc a b) : a ^ (m + 1) ≤ model t := by
    exact (pow_le_pow_left₀ ha.le ht.1 _).trans
      (comparisonModelVolume_bounds m hc (ha.le.trans ht.1)).1
  have hcross (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (_ht : t ∈ Icc a b) (hst : s ≤ t) :
      μ.real (ball x t) * model s ≤ μ.real (ball x s) * model t :=
    hBG x s t (ha.trans_le hs.1) hst
  have hLip := volume_profile_lipschitzOn (pow_pos ha _) measureReal_nonneg K hmono
    (fun _ _ => measureReal_nonneg) hupper hmodel hK hcross
  rw [← uIcc_of_le hab] at hLip
  exact hLip.absolutelyContinuousOnInterval

/-- Euclidean-normalized volume retains absolute continuity on positive
radius intervals; this does not assume monotonicity of that normalization. -/
theorem normalized_ball_volume_absolutelyContinuous {μ : Measure X} (m : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hBG : BallVolumeComparison μ (comparisonModelVolume m c)) (x : X)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hfin : μ (ball x b) ≠ ∞) :
    AbsolutelyContinuousOnInterval (fun t => μ.real (ball x t) / t ^ (m + 1)) a b := by
  have hV := ball_volume_absolutelyContinuous m hc hBG x ha hab hfin
  have hpow : ContDiffOn ℝ 1 (fun t : ℝ => (t ^ (m + 1))⁻¹) (uIcc a b) := by
    apply (contDiffOn_id.pow (m + 1)).inv
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact pow_ne_zero _ (ne_of_gt (ha.trans_le ht.1))
  have hm := hV.mul hpow.absolutelyContinuousOnInterval
  change AbsolutelyContinuousOnInterval
    (fun t => μ.real (ball x t) * (t ^ (m + 1))⁻¹) a b at hm
  simpa only [div_eq_mul_inv] using hm

variable [BorelSpace X] [ProperSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

/-- Bishop--Gromov with a positive continuous model excludes mass on every
positive-radius sphere, not merely almost every sphere. -/
theorem sphere_measure_zero_of_comparison {model : ℝ → ℝ}
    (hBG : BallVolumeComparison μ model) (hcont : Continuous model)
    (x : X) {r : ℝ} (hr : 0 < r) (hmodel : 0 < model r) : μ (sphere x r) = 0 := by
  have hle : μ.real (closedBall x r) * model r ≤ μ.real (ball x r) * model r := by
    have ht : Tendsto (fun i : ℕ => r + 1 / ((i : ℝ) + 1)) atTop (𝓝 r) := by
      simpa only [add_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add r
    apply ge_of_tendsto (tendsto_const_nhds.mul (hcont.continuousAt.tendsto.comp ht))
    apply Eventually.of_forall
    intro i
    have hd : r < r + 1 / ((i : ℝ) + 1) := lt_add_of_pos_right _ (by positivity)
    calc
      μ.real (closedBall x r) * model r ≤
          μ.real (ball x (r + 1 / ((i : ℝ) + 1))) * model r :=
        mul_le_mul_of_nonneg_right
          (measureReal_mono (closedBall_subset_ball hd) measure_ball_lt_top.ne) hmodel.le
      _ ≤ _ := hBG x r _ hr hd.le
  have hreal : μ.real (closedBall x r) = μ.real (ball x r) :=
    le_antisymm ((mul_le_mul_iff_left₀ hmodel).mp hle)
      (measureReal_mono ball_subset_closedBall (isCompact_closedBall x r).measure_ne_top)
  have hm : μ (closedBall x r) = μ (ball x r) :=
    (measureReal_eq_measureReal_iff (isCompact_closedBall x r).measure_ne_top
      measure_ball_lt_top.ne).mp hreal
  rw [← closedBall_sdiff_ball, measure_sdiff ball_subset_closedBall
    isOpen_ball.measurableSet.nullMeasurableSet measure_ball_lt_top.ne, hm, tsub_self]

end RegularPointCoordinates

end

end OAI
