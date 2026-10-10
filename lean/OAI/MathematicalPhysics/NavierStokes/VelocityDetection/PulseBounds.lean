import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SmoothProfiles

namespace OAI

noncomputable section
namespace VelocityDetection.SmoothProfiles
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators

theorem compactSupport_iteratedPulse (m : ℕ) : HasCompactSupport (iteratedDeriv m pulse) := by
  induction m with
  | zero => simpa only [iteratedDeriv_zero] using compactSupport_pulse
  | succ m ih => simpa only [iteratedDeriv_succ] using ih.deriv

theorem positive_derivatives_bounded (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |iteratedDeriv (m + 1) step t| ≤ B := by
  obtain ⟨B, hB⟩ := (compactSupport_iteratedPulse m).exists_bound_of_continuous
    ((contDiff_infty.mp contDiff_pulse m).continuous_iteratedDeriv' m)
  refine ⟨max B 0, le_max_right _ _, fun t => ?_⟩
  simpa only [iteratedDeriv_succ', pulse, Real.norm_eq_abs] using (hB t).trans (le_max_left B 0)

theorem iteratedDeriv_affine {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (A B : ℝ) (m : ℕ) :
    iteratedDeriv m (fun t => f (A * t + B)) =
      fun t => A ^ m * iteratedDeriv m f (A * t + B) := by
  have hf' : ContDiff ℝ m (fun t => f (t + B)) :=
    (contDiff_infty.mp hf m).comp (by fun_prop)
  simpa only [iteratedDeriv_comp_add_const] using
    (iteratedDeriv_comp_const_mul hf' A)

end VelocityDetection.SmoothProfiles
end

end OAI
