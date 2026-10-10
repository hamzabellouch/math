import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingMovingCutoff
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Compact concentration tests tend to one on the plane, and recover the
mass of every integrable scalar by dominated convergence. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Set MeasureTheory Filter
open scoped Topology

theorem concentrationCutoff_eventually_one (c x : Plane) :
    ∀ᶠ n : ℕ in atTop, concentrationCutoff ((n : ℝ) + 1) c x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (3 * ‖x - c‖)
  filter_upwards [eventually_ge_atTop N] with n hn
  apply concentrationCutoff_one (by positivity)
  intro j
  have hcoord : |x j - c j| ≤ ‖x - c‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x - c) j
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [norm_nonneg (x - c)]

theorem concentrationCutoff_tendsto_one (c x : Plane) :
    Tendsto (fun n : ℕ => concentrationCutoff ((n : ℝ) + 1) c x) atTop (𝓝 1) := by
  have he : (fun n : ℕ => concentrationCutoff ((n : ℝ) + 1) c x) =ᶠ[atTop]
      (fun _ => 1) := concentrationCutoff_eventually_one c x
  exact tendsto_const_nhds.congr' he.symm

theorem concentrationCutoff_integral_limit {f : Plane → ℝ} (hf : Integrable f) (c : Plane) :
    Tendsto (fun n : ℕ => ∫ x, concentrationCutoff ((n : ℝ) + 1) c x * f x)
      atTop (𝓝 (∫ x, f x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => |f x|)
  · intro n
    exact (concentrationCutoff_smooth _ _).continuous.aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  · simpa only [Real.norm_eq_abs] using hf.norm
  · intro n
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (concentrationCutoff_range ((n : ℝ) + 1) c x).1]
    calc
      _ ≤ 1 * |f x| := mul_le_mul_of_nonneg_right
        (concentrationCutoff_range ((n : ℝ) + 1) c x).2 (abs_nonneg _)
      _ = _ := one_mul _
  · filter_upwards [] with x
    simpa only [one_mul] using (concentrationCutoff_tendsto_one c x).mul_const (f x)

end ForcedComputation.ExpandingDetector

end

end OAI
