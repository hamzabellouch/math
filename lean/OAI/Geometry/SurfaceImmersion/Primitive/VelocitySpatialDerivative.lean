import OAI.Geometry.SurfaceImmersion.Primitive.VelocityNormalEstimates

namespace OAI

/-! Exact spatial differentiation of the actual circular velocity, separating
all dependence on the angular derivative from the bounded remainder. -/
noncomputable section
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def spatialError (Q : E → Vec) (R : E → ℝ) (e₁ e₂ : E → Vec)
    (α : E → ℝ) (x v : E) : Vec :=
  fderiv ℝ Q x v + (fderiv ℝ R x v) • direction (e₁ x) (e₂ x) (α x) +
    R x • (Real.cos (α x) • fderiv ℝ e₁ x v + Real.sin (α x) • fderiv ℝ e₂ x v)

theorem circular_velocity_derivative {Q : E → Vec} {R : E → ℝ}
    {e₁ e₂ : E → Vec} {α : E → ℝ} {x : E}
    (hQ : DifferentiableAt ℝ Q x) (hR : DifferentiableAt ℝ R x)
    (h₁ : DifferentiableAt ℝ e₁ x) (h₂ : DifferentiableAt ℝ e₂ x)
    (hα : DifferentiableAt ℝ α x) (v : E) :
    fderiv ℝ (fun y => Q y + R y • direction (e₁ y) (e₂ y) (α y)) x v =
      spatialError Q R e₁ e₂ α x v +
        (R x * fderiv ℝ α x v) • angularDirection (e₁ x) (e₂ x) (α x) := by
  have hd := hQ.hasFDerivAt.add (hR.hasFDerivAt.smul
    ((hα.hasFDerivAt.cos.smul h₁.hasFDerivAt).add
      (hα.hasFDerivAt.sin.smul h₂.hasFDerivAt)))
  change HasFDerivAt (fun y => Q y + R y • direction (e₁ y) (e₂ y) (α y)) _ x at hd
  rw [hd.fderiv]
  ext i
  simp only [spatialError, direction, angularDirection, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply', smul_eq_mul,
    neg_mul]
  ring

lemma norm_direction_le (e₁ e₂ : Vec) (α : ℝ) :
    ‖direction e₁ e₂ α‖ ≤ ‖e₁‖ + ‖e₂‖ := by
  calc
    ‖direction e₁ e₂ α‖ ≤ ‖Real.cos α • e₁‖ + ‖Real.sin α • e₂‖ := norm_add_le _ _
    _ ≤ ‖e₁‖ + ‖e₂‖ := add_le_add
      (by rw [norm_smul, Real.norm_eq_abs]; exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one α))
      (by rw [norm_smul, Real.norm_eq_abs]; exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one α))

/-- The bound does not contain a derivative of `α`. -/
theorem spatialError_bound (Q : E → Vec) (R : E → ℝ) (e₁ e₂ : E → Vec)
    (α : E → ℝ) (x v : E) :
    ‖spatialError Q R e₁ e₂ α x v‖ ≤
      ‖fderiv ℝ Q x v‖ + |fderiv ℝ R x v| * (‖e₁ x‖ + ‖e₂ x‖) +
        |R x| * (‖fderiv ℝ e₁ x v‖ + ‖fderiv ℝ e₂ x v‖) := by
  unfold spatialError
  calc
    ‖fderiv ℝ Q x v + (fderiv ℝ R x v) • direction (e₁ x) (e₂ x) (α x) +
        R x • (Real.cos (α x) • fderiv ℝ e₁ x v + Real.sin (α x) • fderiv ℝ e₂ x v)‖
      ≤ ‖fderiv ℝ Q x v‖ + ‖(fderiv ℝ R x v) • direction (e₁ x) (e₂ x) (α x)‖ +
        ‖R x • (Real.cos (α x) • fderiv ℝ e₁ x v + Real.sin (α x) • fderiv ℝ e₂ x v)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ ‖fderiv ℝ Q x v‖ + |fderiv ℝ R x v| * (‖e₁ x‖ + ‖e₂ x‖) +
        |R x| * (‖fderiv ℝ e₁ x v‖ + ‖fderiv ℝ e₂ x v‖) := by
      simp only [norm_smul, Real.norm_eq_abs]
      exact add_le_add (add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left (norm_direction_le _ _ _) (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left (norm_direction_le _ _ _) (abs_nonneg _))

end ClosedSurfaceR4.VelocityFrame

end

end OAI
