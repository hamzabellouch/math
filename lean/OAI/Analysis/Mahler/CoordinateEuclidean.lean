import OAI.Analysis.Mahler.CoordinateSphere
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

noncomputable section
open Set Metric
namespace MahlerStokes

/-- Explicit identification with the L2 Euclidean norm, rather than the
ambient supremum norm on the coordinate function space. -/
theorem radiusSq_eq_euclidean_norm_sq {n : ℕ} (x : Fin n → ℝ) :
    radiusSq x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖^2 := by
  simp [EuclideanSpace.real_norm_sq_eq, radiusSq]

theorem coordBall_eq_euclidean_ball {n : ℕ} {R : ℝ} (hR : 0 ≤ R) :
    coordBall n R = (fun x : Fin n → ℝ => (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))) ⁻¹'
      ball 0 R := by
  ext x
  change radiusSq x < R^2 ↔ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) - 0‖ < R
  rw [sub_zero, radiusSq_eq_euclidean_norm_sq]
  exact sq_lt_sq₀ (norm_nonneg _) hR

theorem coordClosedBall_eq_euclidean_closedBall {n : ℕ} {R : ℝ} (hR : 0 ≤ R) :
    coordClosedBall n R = (fun x : Fin n → ℝ => (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))) ⁻¹'
      closedBall 0 R := by
  ext x
  change radiusSq x ≤ R^2 ↔ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) - 0‖ ≤ R
  rw [sub_zero, radiusSq_eq_euclidean_norm_sq]
  exact sq_le_sq₀ (norm_nonneg _) hR

end MahlerStokes

end

end OAI
