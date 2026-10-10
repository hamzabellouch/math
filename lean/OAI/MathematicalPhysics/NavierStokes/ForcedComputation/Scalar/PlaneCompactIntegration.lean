import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarHamiltonian
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarMassCalculus

namespace OAI

/-! Integration by parts against a compact scalar test function on the
whole plane. The diffusing scalar itself need not have compact support. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian Set MeasureTheory
open scoped ContDiff BigOperators

theorem spatialD_mul {f g : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (j : Fin 2) (x : Plane) :
    spatialD j (fun y => f y * g y) x =
      f x * spatialD j g x + g x * spatialD j f x := by
  unfold spatialD
  have hd := (hf.differentiable (by simp) x).hasFDerivAt.mul
    (hg.differentiable (by simp) x).hasFDerivAt
  change HasFDerivAt (fun y => f y * g y) _ x at hd
  rw [hd.fderiv]
  rfl

theorem integral_compact_spatialD {φ g : Plane → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport φ) (j : Fin 2) :
    (∫ x, φ x * spatialD j g x) = -(∫ x, g x * spatialD j φ x) := by
  have hi : Integrable (fun x => φ x * spatialD j g x) :=
    (hφ.mul (spatialD_smooth j hg)).continuous.integrable_of_hasCompactSupport hc.mul_right
  have hj : Integrable (fun x => g x * spatialD j φ x) :=
    (hg.mul (spatialD_smooth j hφ)).continuous.integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ (basis j)).mul_left
  have hz := spatialD_integral_eq_zero (hφ.mul hg) hc.mul_right j
  have he : spatialD j (fun x => φ x * g x) =
      fun x => φ x * spatialD j g x + g x * spatialD j φ x :=
    funext (spatialD_mul hφ hg j)
  rw [he, integral_add hi hj] at hz
  linarith

theorem integral_compact_second_spatialD {φ g : Plane → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport φ) (j : Fin 2) :
    (∫ x, φ x * spatialD j (spatialD j g) x) =
      ∫ x, g x * spatialD j (spatialD j φ) x := by
  calc
    _ = -(∫ x, spatialD j g x * spatialD j φ x) :=
      integral_compact_spatialD hφ (spatialD_smooth j hg) hc j
    _ = -(∫ x, spatialD j φ x * spatialD j g x) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      exact mul_comm _ _
    _ = -(-(∫ x, g x * spatialD j (spatialD j φ) x)) := by
      rw [integral_compact_spatialD (spatialD_smooth j hφ) hg
        (hc.fderiv_apply ℝ (basis j)) j]
    _ = _ := neg_neg _

theorem integral_compact_laplacian {φ g : Plane → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport φ) :
    (∫ x, φ x * scalarLaplacian g x) = ∫ x, g x * scalarLaplacian φ x := by
  have hi (j : Fin 2) : Integrable (fun x => φ x * spatialD j (spatialD j g) x) :=
    (hφ.mul (spatialD_smooth j (spatialD_smooth j hg))).continuous.integrable_of_hasCompactSupport hc.mul_right
  have hj (j : Fin 2) : Integrable (fun x => g x * spatialD j (spatialD j φ) x) :=
    (hg.mul (spatialD_smooth j (spatialD_smooth j hφ))).continuous.integrable_of_hasCompactSupport
        ((hc.fderiv_apply ℝ (basis j)).fderiv_apply ℝ (basis j)).mul_left
  simp only [scalarLaplacian, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun j _ => hi j), integral_finsetSum Finset.univ (fun j _ => hj j)]
  exact Finset.sum_congr rfl (fun j _ => integral_compact_second_spatialD hφ hg hc j)

end ForcedComputation.VelocityDetector

end

end OAI
