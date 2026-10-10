import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.EuclideanFlowBounds

namespace OAI

/-! The Hessian chain rule used for a transported detector bump. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open scoped ContDiff

theorem scalar_second_composition {g : EuclideanPlane → ℝ}
    {φ : EuclideanPlane → EuclideanPlane} (hg : ContDiff ℝ ∞ g)
    (hφ : ContDiff ℝ ∞ φ) (x v w : EuclideanPlane) :
    fderiv ℝ (fderiv ℝ (g ∘ φ)) x v w =
      fderiv ℝ g (φ x) (fderiv ℝ (fderiv ℝ φ) x v w) +
      fderiv ℝ (fderiv ℝ g) (φ x) (fderiv ℝ φ x v) (fderiv ℝ φ x w) := by
  have he : fderiv ℝ (g ∘ φ) =
      fun y => (fderiv ℝ g (φ y)).comp (fderiv ℝ φ y) := by
    funext y
    exact fderiv_comp y (hg.differentiable (by simp) _) (hφ.differentiable (by simp) _)
  rw [he]
  have hg' := ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp) (φ x)).hasFDerivAt
  have hφ' := ((hφ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt
  have hd := (hg'.comp x ((hφ.differentiable (by simp) x).hasFDerivAt)).clm_comp hφ'
  simp only [Function.comp_def] at hd
  rw [hd.fderiv]
  rfl

theorem scalar_second_composition_bound {g : EuclideanPlane → ℝ}
    {φ : EuclideanPlane → EuclideanPlane} (hg : ContDiff ℝ ∞ g)
    (hφ : ContDiff ℝ ∞ φ) (x : EuclideanPlane) {A B P Q : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hg₁ : ‖fderiv ℝ g (φ x)‖ ≤ A) (hg₂ : ‖fderiv ℝ (fderiv ℝ g) (φ x)‖ ≤ B)
    (hφ₁ : ‖fderiv ℝ φ x‖ ≤ P) (hφ₂ : ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ Q) :
    ‖fderiv ℝ (fderiv ℝ (g ∘ φ)) x‖ ≤ A * Q + B * P ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [scalar_second_composition hg hφ]
  have hvb : ‖fderiv ℝ φ x v‖ ≤ P * ‖v‖ :=
    ((fderiv ℝ φ x).le_opNorm v).trans (mul_le_mul_of_nonneg_right hφ₁ (norm_nonneg v))
  have hwb : ‖fderiv ℝ φ x w‖ ≤ P * ‖w‖ :=
    ((fderiv ℝ φ x).le_opNorm w).trans (mul_le_mul_of_nonneg_right hφ₁ (norm_nonneg w))
  calc
    _ ≤ ‖fderiv ℝ g (φ x) (fderiv ℝ (fderiv ℝ φ) x v w)‖ +
        ‖fderiv ℝ (fderiv ℝ g) (φ x) (fderiv ℝ φ x v) (fderiv ℝ φ x w)‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ g (φ x)‖ * (‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖v‖ * ‖w‖) +
        ‖fderiv ℝ (fderiv ℝ g) (φ x)‖ * ‖fderiv ℝ φ x v‖ * ‖fderiv ℝ φ x w‖ := by
      apply add_le_add
      · exact ((fderiv ℝ g (φ x)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left ((fderiv ℝ (fderiv ℝ φ) x).le_opNorm₂ v w) (norm_nonneg _))
      · exact (fderiv ℝ (fderiv ℝ g) (φ x)).le_opNorm₂ _ _
    _ ≤ A * (Q * ‖v‖ * ‖w‖) + B * (P * ‖v‖) * (P * ‖w‖) := by
      apply add_le_add
      · exact mul_le_mul hg₁
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hφ₂ (norm_nonneg v)) (norm_nonneg w))
          (by positivity) hA
      · exact mul_le_mul (mul_le_mul hg₂ hvb (norm_nonneg _) hB) hwb
          (norm_nonneg _) (mul_nonneg hB (mul_nonneg hP (norm_nonneg v)))
    _ = ((A * Q + B * P ^ 2) * ‖v‖) * ‖w‖ := by ring

end ForcedComputation.VelocityDetector

end

end OAI
