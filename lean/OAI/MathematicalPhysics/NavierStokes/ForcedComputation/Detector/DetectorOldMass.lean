import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorMass
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorSchedule
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarTimeWindow
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorMargins

namespace OAI

/-! The heat-only wait bounds all older injections uniformly before the
next burst. The first burst starts with the scalar identically zero. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem detectorSource_before_two (C L : ℕ) {t : ℝ} (ht : t ≤ 2) (x : Plane) :
    detectorSource C L t x = 0 := by
  change (∑' n, detectorSourceTerm C L n (t, x)) = 0
  trans (∑' _ : ℕ, (0 : ℝ))
  swap
  · exact tsum_zero
  apply tsum_congr
  intro n
  apply detectorSourceTerm_before_closed
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  change t ≤ 2 * ((n : ℝ) + 1)
  linarith

theorem detector_scalar_before_two {V : ℝ → Plane → Plane} (C L : ℕ)
    {w : ℝ → Plane → ℝ}
    (hs : GlobalTorusScalarSolution 1 (detectorDrift V C L) (detectorSource C L)
      w (fun _ => 0)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) (x : Plane) : w t x = 0 := by
  have hb := (hs 2 (by norm_num)).absolute_bound (by norm_num) (by norm_num)
    (M := 0) (A := 0)
    (fun s hs' y => by simp only [detectorSource_before_two C L hs'.2 y, abs_zero, le_refl])
    (fun _ => by simp) t ht x
  have hz : |w t x| ≤ 0 := by simpa only [zero_mul, zero_add] using hb
  exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))

theorem detector_scalar_at_start_bound (hK : TorusHeatInput)
    {V : ℝ → Plane → Plane} (hV : ContDiff ℝ ∞ (Function.uncurry V))
    (hp : ∀ s, PlanePeriodic (V s))
    (hdiv : ∀ s x, PlanarHamiltonian.divergence (V s) x = 0)
    (C L : ℕ) {w : ℝ → Plane → ℝ}
    (hs : GlobalTorusScalarSolution 1 (detectorDrift V C L) (detectorSource C L)
      w (fun _ => 0)) (hw : ContDiff ℝ ∞ (Function.uncurry w))
    (n : ℕ) (x : Plane) :
    |w (2 * ((n : ℝ) + 1)) x| ≤ 16 * (massBound L : ℝ) := by
  have hn := hs.nonnegative (by norm_num : (0 : ℝ) ≤ 1)
    (fun t _ y => detectorSource_nonnegative C L t y) (fun _ => le_rfl)
  cases n with
  | zero =>
    have hz := (hs 2 (by norm_num)).absolute_bound (by norm_num) (by norm_num)
      (M := 0) (A := 0)
      (fun t ht y => by simp only [detectorSource_before_two C L ht.2 y, abs_zero, le_refl])
      (fun _ => by simp) 2 (by norm_num) x
    have hm := (massBound_real_small L).1
    norm_num only [Nat.cast_zero, zero_add, mul_one, zero_mul, add_zero] at hz ⊢
    linarith
  | succ m =>
    let S : ℝ := 2 * ((m : ℝ) + 1) + 2 * (duration C L m : ℝ)
    let T : ℝ := 2 - 2 * (duration C L m : ℝ)
    have hd : (0 : ℝ) < duration C L m := by exact_mod_cast duration_pos C L m
    have hT : 1 < T := by
      have hδ := detector_duration_real_le C L m
      dsimp only [T]
      linarith
    have hS : 0 ≤ S := by dsimp only [S]; positivity
    have he : S + T = 2 * (((m + 1 : ℕ) : ℝ) + 1) := by
      dsimp only [S, T]
      push_cast
      ring
    have hz (r : ℝ) (hr : r ∈ Icc (0 : ℝ) T) (y : Plane) :
        detectorDrift V C L (S + r) y = 0 ∧ detectorSource C L (S + r) y = 0 := by
      apply detector_wait_coefficients_zero V C L m
      dsimp only [S, T] at *
      constructor <;> linarith [hr.1, hr.2]
    have hheat := hs.heat_window hK hw hS (by linarith : 0 ≤ T)
      (fun r hr => funext (fun y => (hz r hr y).1))
      (fun r hr => funext (fun y => (hz r hr y).2)) T ⟨by linarith, le_rfl⟩
    rw [← he, abs_of_nonneg (hn (S + T) (add_nonneg hS (by linarith)) x), hheat]
    have hb := torusHeatEvolution_after_one hK
      (hw.comp (contDiff_const.prodMk contDiff_id)).continuous
      (hn S hS) hT.le x
    exact hb.trans (mul_le_mul_of_nonneg_left
      (detector_scalar_mass_bound hV hp hdiv C L hs hw hS) (by norm_num))

end ForcedComputation.VelocityDetector

end

end OAI
