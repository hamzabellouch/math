import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorBump
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorBlockSum
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.VelocityDetectorScales

namespace OAI

/-! The scalar source installs every test block without simulating the
machine. Its locally finite sum is smooth, periodic, and nonnegative. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows
open scoped ContDiff

theorem detector_width_small (L n : ℕ) : (width L n : ℝ) ≤ 1 / 16 := by
  have hw := width_le L n
  have hp : (1 / 2 : ℚ) ^ (n + 1) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have h : width L n ≤ 1 / 16 := by nlinarith
  have hh := (Rat.cast_le (K := ℝ)).mpr h
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hh
  exact hh

def detectorSourceTerm (C L n : ℕ) (y : ℝ × Plane) : ℝ :=
  (duration C L n : ℝ)⁻¹ *
    smoothPulse 0 1 ((y.1 - 2 * ((n : ℝ) + 1)) / (duration C L n : ℝ)) *
      detectorBump (width L n : ℝ) y.2

def detectorSource (C L : ℕ) (t : ℝ) (x : Plane) : ℝ :=
  detectorBlockSum (detectorSourceTerm C L) (t, x)

theorem detectorSourceTerm_smooth (C L n : ℕ) :
    ContDiff ℝ ∞ (detectorSourceTerm C L n) := by
  have hb : (0 : ℝ) < width L n := by exact_mod_cast width_pos L n
  exact (contDiff_const.mul ((smoothPulse_smooth 0 1).comp
    ((contDiff_fst.sub contDiff_const).div_const _))).mul
      ((detectorBump_smooth hb).comp contDiff_snd)

theorem detectorSourceTerm_before (C L n : ℕ) (y : ℝ × Plane)
    (hy : y.1 < 2 * ((n : ℝ) + 1)) : detectorSourceTerm C L n y = 0 := by
  have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
  have harg : (y.1 - 2 * ((n : ℝ) + 1)) / (duration C L n : ℝ) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  simp only [detectorSourceTerm, smoothPulse_before (by norm_num : (0 : ℝ) < 1) harg,
    mul_zero, zero_mul]

theorem detectorSourceTerm_nonnegative (C L n : ℕ) (y : ℝ × Plane) :
    0 ≤ detectorSourceTerm C L n y := by
  have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
  have hb : (0 : ℝ) < width L n := by exact_mod_cast width_pos L n
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hd.le)
    (smoothPulse_nonneg (by norm_num : (0 : ℝ) < 1) _))
    (detectorBump_range hb (detector_width_small L n) y.2).1

theorem detectorSource_smooth (C L : ℕ) :
    ContDiff ℝ ∞ (Function.uncurry (detectorSource C L)) :=
  detectorBlockSum_smooth _ (detectorSourceTerm_smooth C L) (detectorSourceTerm_before C L)

theorem detectorSource_nonnegative (C L : ℕ) (t : ℝ) (x : Plane) :
    0 ≤ detectorSource C L t x :=
  tsum_nonneg (fun n => detectorSourceTerm_nonnegative C L n (t, x))

theorem detectorSource_periodic (C L : ℕ) (t : ℝ) : PlanePeriodic (detectorSource C L t) := by
  intro x k
  unfold detectorSource detectorBlockSum
  apply tsum_congr
  intro n
  simp only [detectorSourceTerm, detectorBump_periodic (width L n : ℝ) x k]

theorem detectorSource_before (C L : ℕ) {t : ℝ} (ht : t ≤ 0) (x : Plane) :
    detectorSource C L t x = 0 := by
  change (∑' n, detectorSourceTerm C L n (t, x)) = 0
  trans (∑' _ : ℕ, (0 : ℝ))
  swap
  · exact tsum_zero
  apply tsum_congr
  intro n
  apply detectorSourceTerm_before
  change t < 2 * ((n : ℝ) + 1)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem detectorSource_before_one (C L : ℕ) {t : ℝ} (ht : t ≤ 1) (x : Plane) :
    detectorSource C L t x = 0 := by
  change (∑' n, detectorSourceTerm C L n (t, x)) = 0
  trans (∑' _ : ℕ, (0 : ℝ))
  swap
  · exact tsum_zero
  apply tsum_congr
  intro n
  apply detectorSourceTerm_before
  change t < 2 * ((n : ℝ) + 1)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

end ForcedComputation.VelocityDetector

end

end OAI
