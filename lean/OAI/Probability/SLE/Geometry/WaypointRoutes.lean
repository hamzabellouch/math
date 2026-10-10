import OAI.Probability.SLE.Gauge.RibbonRouteLifting
import OAI.Probability.SLE.Gauge.RibbonSideCorridors
import OAI.Probability.SLE.Geometry.CompactTubeProbability

namespace OAI

/-! Explicit bounded-speed routes from the waypoint to either side of the
core and then across it behind the front. These are the deterministic
templates for the two Brownian tube events in the waypoint argument. -/

noncomputable section
open Set Metric
open scoped Topology NNReal BoundedContinuousFunction ENNReal

namespace SLEExactGauge.RibbonCoordinates
open RectangleCrossing

def unitClip (t : ℝ) : ℝ := max 0 (min 1 t)

theorem unitClip_lipschitz : LipschitzWith 1 unitClip :=
  (LipschitzWith.id.const_min 1).const_max 0

theorem unitClip_nonneg (t : ℝ) : 0 ≤ unitClip t := le_max_left _ _

theorem unitClip_le_one (t : ℝ) : unitClip t ≤ 1 := by
  exact max_le (by norm_num) (min_le_left _ _)

theorem unitClip_of_nonpos {t : ℝ} (ht : t ≤ 0) : unitClip t = 0 := by
  exact max_eq_left ((min_le_right _ _).trans ht)

theorem unitClip_of_one_le {t : ℝ} (ht : 1 ≤ t) : unitClip t = 1 := by
  rw [unitClip, min_eq_left ht, max_eq_right (by norm_num)]

theorem unitClip_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : unitClip t = t := by
  rw [unitClip, min_eq_right ht.2, max_eq_right ht.1]

def waypointRoute (k side t : ℝ) : ℂ :=
  (((k + 1 / 2 - unitClip (t - 1) : ℝ) : ℂ)) +
    (((side * (unitClip t / 2 - unitClip (t - 2)) : ℝ) : ℂ)) * Complex.I

@[simp] theorem waypointRoute_re (k side t : ℝ) :
    (waypointRoute k side t).re = k + 1 / 2 - unitClip (t - 1) := by
  simp [waypointRoute]

@[simp] theorem waypointRoute_im (k side t : ℝ) :
    (waypointRoute k side t).im = side * (unitClip t / 2 - unitClip (t - 2)) := by
  simp [waypointRoute]

theorem waypointRoute_zero (k side : ℝ) : waypointRoute k side 0 = ((k + 1 / 2 : ℝ) : ℂ) := by
  norm_num [waypointRoute, unitClip]

theorem waypointRoute_continuous (k side : ℝ) : Continuous (waypointRoute k side) := by
  have hc := unitClip_lipschitz.continuous
  unfold waypointRoute
  fun_prop

theorem waypointRoute_lipschitz (k side : ℝ) (hside : |side| = 1) :
    LipschitzWith 3 (waypointRoute k side) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have h₀ := unitClip_lipschitz.dist_le_mul u v
  have h₁ := unitClip_lipschitz.dist_le_mul (u - 1) (v - 1)
  have h₂ := unitClip_lipschitz.dist_le_mul (u - 2) (v - 2)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, sub_sub_sub_cancel_right] at h₀ h₁ h₂
  have him : |side * (unitClip u / 2 - unitClip (u - 2)) -
      side * (unitClip v / 2 - unitClip (v - 2))| ≤ 3 / 2 * |u - v| := by
    rw [← mul_sub, abs_mul, hside, one_mul]
    have he : (unitClip u / 2 - unitClip (u - 2)) -
        (unitClip v / 2 - unitClip (v - 2)) =
        (unitClip u - unitClip v) / 2 - (unitClip (u - 2) - unitClip (v - 2)) := by ring
    rw [he]
    have hh := abs_sub ( (unitClip u - unitClip v) / 2) (unitClip (u - 2) - unitClip (v - 2))
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
    linarith
  have hre : |(k + 1 / 2 - unitClip (u - 1)) -
      (k + 1 / 2 - unitClip (v - 1))| ≤ |u - v| := by
    simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using h₁
  have hh := Complex.norm_le_abs_re_add_abs_im (waypointRoute k side u - waypointRoute k side v)
  simp only [Complex.sub_re, Complex.sub_im, waypointRoute_re, waypointRoute_im] at hh
  rw [dist_eq_norm, Real.dist_eq]
  norm_num only [NNReal.coe_ofNat]
  nlinarith [abs_nonneg (u - v)]

theorem waypointRoute_im_bound (k side : ℝ) (hside : |side| = 1) (t : ℝ) :
    |(waypointRoute k side t).im| ≤ 1 / 2 := by
  rw [waypointRoute_im, abs_mul, hside, one_mul]
  have h₀ := unitClip_nonneg t
  have h₁ := unitClip_le_one t
  have h₂ := unitClip_nonneg (t - 2)
  have h₃ := unitClip_le_one (t - 2)
  by_cases ht : t ≤ 2
  · rw [unitClip_of_nonpos (by linarith : t - 2 ≤ 0), sub_zero, abs_of_nonneg (by positivity)]
    linarith
  · rw [unitClip_of_one_le (by linarith : 1 ≤ t)]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem waypointRoute_mem_patch (k side : ℝ) (hside : |side| = 1) (t : ℝ) :
    waypointRoute k side t ∈ crossingPatch k := by
  have h₀ := unitClip_nonneg (t - 1)
  have h₁ := unitClip_le_one (t - 1)
  refine ⟨?_, ?_, (waypointRoute_im_bound k side hside t).trans (by norm_num)⟩
  · rw [waypointRoute_re]; linarith
  · rw [waypointRoute_re]; linarith

/-- The final leg is the fixed transverse template, with one orientation
for each side. -/
theorem waypointRoute_final_negative (k : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    waypointRoute k (-1) (2 + t) = transverseTemplate k t := by
  have h₁ : unitClip (2 + t - 1) = 1 := unitClip_of_one_le (by linarith [ht.1])
  have h₂ : unitClip (2 + t) = 1 := unitClip_of_one_le (by linarith [ht.1])
  have h₃ : unitClip (2 + t - 2) = t := by simpa using unitClip_of_mem ht
  unfold waypointRoute transverseTemplate
  rw [h₁, h₂, h₃]
  push_cast
  ring

theorem waypointRoute_final_positive (k : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    waypointRoute k 1 (3 - t) = transverseTemplate k t := by
  have h₁ : unitClip (3 - t - 1) = 1 := unitClip_of_one_le (by linarith [ht.2])
  have h₂ : unitClip (3 - t) = 1 := unitClip_of_one_le (by linarith [ht.2])
  have h₃ : unitClip (3 - t - 2) = 1 - t := by
    rw [show 3 - t - 2 = 1 - t by ring]
    exact unitClip_of_mem ⟨by linarith [ht.2], by linarith [ht.1]⟩
  unfold waypointRoute transverseTemplate
  rw [h₁, h₂, h₃]
  push_cast
  ring

end SLEExactGauge.RibbonCoordinates

end

end OAI
