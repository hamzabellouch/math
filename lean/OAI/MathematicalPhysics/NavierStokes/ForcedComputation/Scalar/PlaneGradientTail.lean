import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHessianTail

namespace OAI

/-! Square integrability of the first spatial derivatives follows from
the same scalar tail, now using the bounded second derivative. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian MeasureTheory
open scoped ContDiff

theorem scalar_gradient_entry_tail {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hfB : ∀ y, |f y| ≤ B * planeTailProfile y)
    (hfM : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ M)
    (x : Plane) (j : Fin 2) :
    |spatialD j f x| ≤ (50 * B + M) * derivativeTail x := by
  have hh := scalar_first_directional_tail hf hB hM hfB hfM x (basis j) (plane_basis_norm_le j)
  simpa only [iteratedFDeriv_one_apply, spatialD] using hh

theorem scalar_gradient_square_integrable {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hfB : ∀ y, |f y| ≤ B * planeTailProfile y)
    (hfM : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ M) (j : Fin 2) :
    Integrable (fun x => (spatialD j f x) ^ 2) := by
  let A := 50 * B + M
  apply (derivativeTail_square_integrable.const_mul (A ^ 2)).mono'
    ((spatialD_smooth j hf).continuous.pow 2).aestronglyMeasurable
  filter_upwards [] with x
  have hb : |spatialD j f x| ≤ A * derivativeTail x :=
    scalar_gradient_entry_tail hf hB hM hfB hfM x j
  have hA : 0 ≤ A * derivativeTail x :=
    mul_nonneg (by dsimp [A]; positivity) (derivativeTail_pos x).le
  have hs := (sq_le_sq₀ (abs_nonneg _) hA).mpr hb
  change ‖spatialD j f x ^ 2‖ ≤ A ^ 2 * derivativeTail x ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (spatialD j f x)]

end ForcedComputation.VelocityDetector

end

end OAI
