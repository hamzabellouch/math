import OAI.Geometry.RCD.Coordinates.RegularNetGeometry

namespace OAI

/-! # Global support separation for the actual heat-coordinate patches -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

namespace RegularBilinearData

variable {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X} [(hausdorff n X).Regular]
  {base : X} {ker : ℝ → X → X → ℝ}
  {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker} {enlargement zeta : ℝ}
  (d : RegularBilinearData hX base hk enlargement zeta)

/-- The working region lies inside the common harmonic neighborhood. -/
theorem patch_region_subset : regularPatchRegion base d.radius d.shift ⊆ ball base (d.radius / 32) := by
  apply ball_subset_ball
  apply div_le_div_of_nonneg_left d.radius_pos.le (by norm_num : (0 : ℝ) < 32)
  have h := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := d.shift)
  rw [pow_add]
  norm_num
  linarith

/-- Pair scales inside the working region follow the common heat index. -/
theorem patch_region_pair_bound {q z : X}
    (hq : q ∈ regularPatchRegion base d.radius d.shift)
    (hz : z ∈ regularPatchRegion base d.radius d.shift) :
    dist z q ≤ (d.radius / (2 : ℝ) ^ d.shift) / 128 := by
  have hR := d.radius_pos
  have heq : d.radius / (2 : ℝ) ^ (d.shift + 10) =
      ((d.radius / (2 : ℝ) ^ d.shift) / 128) / 8 := by
    rw [pow_add]
    norm_num
    ring
  have hq' : dist q base < d.radius / (2 : ℝ) ^ (d.shift + 10) := hq
  have hz' : dist z base < d.radius / (2 : ℝ) ^ (d.shift + 10) := hz
  rw [heq] at hq' hz'
  have hh := dist_triangle z base q
  rw [dist_comm base q] at hh
  have ht : 0 < (d.radius / (2 : ℝ) ^ d.shift) / 128 := by positivity
  linarith

/-- Beyond the net radius, the fine frozen norm separates every pair in
the working region, including pairs outside its approximation ball. -/
theorem net_pair_lower_bound {q z : X}
    (hq : q ∈ regularPatchRegion base d.radius d.shift)
    (hz : z ∈ regularPatchRegion base d.radius d.shift)
    (hzeta : zeta ≤ 1 / 64) (i : ℕ)
    (hfar : regularNetRadius d.radius d.shift i ≤ dist z q) :
    dist z q ≤ 4 * ‖d.frozenAt q i (d.values z - d.values q)‖ := by
  have hR := d.radius_pos
  have hq' := d.patch_region_subset hq
  let a := regularNetRadius d.radius d.shift i
  let t := (d.radius / (2 : ℝ) ^ (d.shift + i + 17)) / 128
  have ha : 0 < a := div_pos d.radius_pos (by positivity)
  have ht : 0 < t := by dsimp only [t]; positivity
  have hta : t = 16 * a := by
    dsimp only [t, a, regularNetRadius]
    rw [show d.shift + i + 28 = (d.shift + i + 17) + 11 by omega, pow_add]
    norm_num
    ring
  by_cases hclose : dist z q ≤ 4 * t
  · have h := d.exact_frame_pair_error hq' (d.shift + i + 17) hclose
    change |‖coordinateFrame (d.frameAt q hq' (d.shift + i + 17)) (d.values z - d.values q)‖ - dist q z| ≤ zeta * t at h
    have hf := (d.mean_heat_frame_comparison q hq' (d.shift + i + 17) (by omega) (d.values z - d.values q)).1
    change ‖coordinateFrame (d.frameAt q hq' (d.shift + i + 17)) (d.values z - d.values q)‖ ≤
      (3 / 2 : ℝ) * ‖d.frozenAt q i (d.values z - d.values q)‖ at hf
    have hs := mul_le_mul_of_nonneg_right hzeta ht.le
    rw [hta] at hs
    have hl := (abs_le.mp h).1
    rw [dist_comm q z, hta] at hl
    change a ≤ dist z q at hfar
    linarith
  · let t0 := (d.radius / (2 : ℝ) ^ d.shift) / 128
    have ht0 : 0 < t0 := by dsimp only [t0]; positivity
    have hscale (j : ℕ) : t0 / (2 : ℝ) ^ j =
        (d.radius / (2 : ℝ) ^ (d.shift + j)) / 128 := by
      dsimp only [t0]
      rw [pow_add]
      ring
    obtain ⟨j, hj, hlow, hhigh⟩ := exists_bounded_dyadic_scale ht0 (lt_of_lt_of_le ha hfar)
      (d.patch_region_pair_bound hq hz) (i + 17) (by rw [hscale]; change t ≤ dist z q; linarith)
    have htj : 0 < t0 / (2 : ℝ) ^ j := div_pos ht0 (by positivity)
    have hr : dist z q ≤ 4 * ((d.radius / (2 : ℝ) ^ (d.shift + j)) / 128) := by
      rw [← hscale]
      linarith
    have h := d.exact_frame_pair_error hq' (d.shift + j) hr
    rw [← hscale] at h
    have hf := d.coarse_frame_le_frozen hq' i (d.shift + j) (by omega) (by omega) (d.values z - d.values q)
    have hs := mul_le_mul_of_nonneg_right hzeta htj.le
    have hl := (abs_le.mp h).1
    rw [dist_comm q z] at hl
    linarith

end RegularBilinearData
end RegularPointCoordinates

end

end OAI
