import OAI.Geometry.RCD.Metric.VolumeComparison
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-!
# Uniformly flat negative-curvature comparison volumes

The dimension is `m + 1`. The radial factor for curvature `-m * a ^ 2`
is written as the primitive of `cosh (a * t)`, which also covers `a = 0`
without a removable singularity. Its volume is normalized by the volume
of the Euclidean unit ball. The bounds below are uniform down to radius
zero, as required before applying almost-volume rigidity.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RegularPointCoordinates

noncomputable def radialComparison (a r : ℝ) : ℝ :=
  ∫ t in 0..r, Real.cosh (a * t)

noncomputable def comparisonModelVolume (m : ℕ) (a r : ℝ) : ℝ :=
  (m + 1 : ℝ) * ∫ t in 0..r, radialComparison a t ^ m

theorem continuous_radialComparison (a : ℝ) : Continuous (radialComparison a) := by
  exact intervalIntegral.continuous_primitive
    (fun b c => (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).intervalIntegrable b c) 0

theorem continuous_comparisonModelVolume (m : ℕ) (a : ℝ) :
    Continuous (comparisonModelVolume m a) := by
  exact continuous_const.mul (intervalIntegral.continuous_primitive
    (fun b c => ((continuous_radialComparison a).pow m).intervalIntegrable b c) 0)

@[simp] theorem radialComparison_zero (r : ℝ) : radialComparison 0 r = r := by
  simp [radialComparison]

theorem radialComparison_eq_sinh {a : ℝ} (ha : a ≠ 0) (r : ℝ) :
    radialComparison a r = Real.sinh (a * r) / a := by
  have hderiv (x : ℝ) : HasDerivAt (fun t => Real.sinh (a * t) / a)
      (Real.cosh (a * x)) x := by
    convert (((hasDerivAt_id x).const_mul a).sinh.div_const a) using 1 <;>
      simp [ha]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x)
    ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 r)
  simpa [radialComparison] using h

theorem radialComparison_bounds {a r R : ℝ} (ha : 0 ≤ a)
    (hr : 0 ≤ r) (hrR : r ≤ R) :
    r ≤ radialComparison a r ∧ radialComparison a r ≤ Real.cosh (a * R) * r := by
  have hcont : Continuous (fun t : ℝ => Real.cosh (a * t)) :=
    Real.continuous_cosh.comp (continuous_const.mul continuous_id)
  constructor
  · have h := intervalIntegral.integral_mono_on (μ := volume) hr
      (continuous_const.intervalIntegrable 0 r) (hcont.intervalIntegrable 0 r)
      (fun t _ => Real.one_le_cosh (a * t))
    simpa [radialComparison] using h
  · have hR : 0 ≤ R := hr.trans hrR
    have h := intervalIntegral.integral_mono_on (μ := volume) hr (hcont.intervalIntegrable 0 r)
      (continuous_const.intervalIntegrable 0 r) (fun t ht => by
        apply Real.cosh_le_cosh.mpr
        rw [abs_of_nonneg (mul_nonneg ha ht.1), abs_of_nonneg (mul_nonneg ha hR)]
        exact mul_le_mul_of_nonneg_left (ht.2.trans hrR) ha)
    simpa [radialComparison, mul_comm] using h

@[simp] theorem comparisonModelVolume_zero (m : ℕ) (r : ℝ) :
    comparisonModelVolume m 0 r = r ^ (m + 1) := by
  simp only [comparisonModelVolume, radialComparison_zero, integral_pow,
    zero_pow (Nat.succ_ne_zero m), sub_zero]
  have hm : (m + 1 : ℝ) ≠ 0 := by positivity
  field_simp

theorem comparisonModelVolume_bounds (m : ℕ) {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) :
    r ^ (m + 1) ≤ comparisonModelVolume m a r ∧
      comparisonModelVolume m a r ≤ Real.cosh (a * r) ^ m * r ^ (m + 1) := by
  have hint : IntervalIntegrable (fun t => radialComparison a t ^ m) volume 0 r :=
    ((continuous_radialComparison a).pow m).intervalIntegrable 0 r
  have hpow : IntervalIntegrable (fun t : ℝ => t ^ m) volume 0 r :=
    (continuous_id.pow m).intervalIntegrable 0 r
  have hflat : (m + 1 : ℝ) * ∫ t in 0..r, t ^ m = r ^ (m + 1) := by
    simpa [comparisonModelVolume] using comparisonModelVolume_zero m r
  have hm : 0 ≤ (m + 1 : ℝ) := by positivity
  constructor
  · rw [← hflat]
    exact mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_on hr hpow hint
      (fun t ht => pow_le_pow_left₀ ht.1 (radialComparison_bounds ha ht.1 ht.2).1 m)) hm
  · have hb := intervalIntegral.integral_mono_on hr hint
      ((continuous_const.mul (continuous_id.pow m)).intervalIntegrable 0 r)
      (fun t ht => by
        have hrad := radialComparison_bounds ha ht.1 ht.2
        calc
          radialComparison a t ^ m ≤ (Real.cosh (a * r) * t) ^ m :=
            pow_le_pow_left₀ (ht.1.trans hrad.1) hrad.2 m
          _ = Real.cosh (a * r) ^ m * t ^ m := mul_pow _ _ _)
    change (∫ t in 0..r, radialComparison a t ^ m) ≤
      ∫ t in 0..r, Real.cosh (a * r) ^ m * t ^ m at hb
    rw [intervalIntegral.integral_const_mul] at hb
    calc
      comparisonModelVolume m a r ≤
          (m + 1 : ℝ) * (Real.cosh (a * r) ^ m * ∫ t in 0..r, t ^ m) :=
        mul_le_mul_of_nonneg_left hb hm
      _ = Real.cosh (a * r) ^ m * ((m + 1 : ℝ) * ∫ t in 0..r, t ^ m) := by ring
      _ = _ := by rw [hflat]

theorem comparisonModelVolume_pos (m : ℕ) {a r : ℝ} (ha : 0 ≤ a) (hr : 0 < r) :
    0 < comparisonModelVolume m a r :=
  (pow_pos hr _).trans_le (comparisonModelVolume_bounds m ha hr.le).1

/-- A single model error at the outer radius controls every smaller
positive radius. There is no positive lower cutoff on the radius. -/
theorem comparisonModelVolume_relative_error (m : ℕ) {a r R : ℝ}
    (ha : 0 ≤ a) (hr : 0 < r) (hrR : r ≤ R) :
    0 ≤ comparisonModelVolume m a r / r ^ (m + 1) - 1 ∧
      comparisonModelVolume m a r / r ^ (m + 1) - 1 ≤ Real.cosh (a * R) ^ m - 1 := by
  have hb := comparisonModelVolume_bounds m ha hr.le
  have hpos : 0 < r ^ (m + 1) := pow_pos hr _
  have hcosh : Real.cosh (a * r) ≤ Real.cosh (a * R) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (mul_nonneg ha hr.le),
      abs_of_nonneg (mul_nonneg ha (hr.le.trans hrR))]
    exact mul_le_mul_of_nonneg_left hrR ha
  constructor
  · have h : 1 ≤ comparisonModelVolume m a r / r ^ (m + 1) :=
      (le_div_iff₀ hpos).mpr (by simpa only [one_mul] using hb.1)
    linarith
  · have h := (div_le_iff₀ hpos).mpr hb.2
    have hp := pow_le_pow_left₀ (Real.cosh_pos _).le hcosh m
    linarith

theorem comparisonModelVolume_uniformly_flat (m : ℕ) {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hazero : Tendsto a atTop (𝓝 0))
    (R : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ i in atTop, ∀ r : ℝ, 0 < r → r ≤ R →
      |comparisonModelVolume m (a i) r / r ^ (m + 1) - 1| < epsilon := by
  have ht0 : Tendsto (fun i => a i * R) atTop (𝓝 0) := by
    simpa only [zero_mul] using hazero.mul_const R
  have ht : Tendsto (fun i => Real.cosh (a i * R) ^ m - 1) atTop (𝓝 0) := by
    simpa using (((Real.continuous_cosh.tendsto 0).comp ht0).pow m).sub_const 1
  filter_upwards [ht.eventually (gt_mem_nhds hepsilon)] with i hi r hr hrR
  have hb := comparisonModelVolume_relative_error m (ha i) hr hrR
  rw [abs_of_nonneg hb.1]
  exact hb.2.trans_lt hi

/-- For a fixed curvature parameter the normalized model volumes tend to
one at small radii, with no division at radius zero. -/
theorem comparisonModelVolume_density (m : ℕ) {a : ℝ} (ha : 0 ≤ a)
    {r : ℕ → ℝ} (hr : ∀ i, 0 < r i) (hrzero : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun i => comparisonModelVolume m a (r i) / r i ^ (m + 1))
      atTop (𝓝 1) := by
  have ht0 : Tendsto (fun i => a * r i) atTop (𝓝 0) := by
    simpa only [mul_zero] using hrzero.const_mul a
  have ht : Tendsto (fun i => Real.cosh (a * r i) ^ m - 1) atTop (𝓝 0) := by
    simpa using (((Real.continuous_cosh.tendsto 0).comp ht0).pow m).sub_const 1
  have herror : Tendsto
      (fun i => comparisonModelVolume m a (r i) / r i ^ (m + 1) - 1) atTop (𝓝 0) :=
    squeeze_zero (fun i => (comparisonModelVolume_relative_error m ha (hr i) le_rfl).1)
      (fun i => (comparisonModelVolume_relative_error m ha (hr i) le_rfl).2) ht
  simpa using herror.add_const 1

end RegularPointCoordinates

end OAI
