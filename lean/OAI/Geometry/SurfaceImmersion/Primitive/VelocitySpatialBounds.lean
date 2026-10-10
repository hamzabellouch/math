import OAI.Geometry.SurfaceImmersion.Primitive.VelocitySpatialDerivative

namespace OAI

/-! Compact bounds for the actual circular velocity derivative, uniform in
both the angle and its arbitrarily large derivatives. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compact_spatialError_bound {Q : E → Vec} {R : E → ℝ} {e₁ e₂ : E → Vec}
    (hQ : ContDiff ℝ ∞ Q) (hR : ContDiff ℝ ∞ R)
    (h₁ : ContDiff ℝ ∞ e₁) (h₂ : ContDiff ℝ ∞ e₂)
    {K : Set E} (hK : IsCompact K) (v : E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : E → ℝ) x, x ∈ K →
      ‖spatialError Q R e₁ e₂ α x v‖ ≤ C := by
  have hDQ : Continuous (fun x => fderiv ℝ Q x v) :=
    ((hQ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hDR : Continuous (fun x => fderiv ℝ R x v) :=
    ((hR.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hD₁ : Continuous (fun x => fderiv ℝ e₁ x v) :=
    ((h₁.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hD₂ : Continuous (fun x => fderiv ℝ e₂ x v) :=
    ((h₂.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  let L : E → ℝ := fun x => ‖fderiv ℝ Q x v‖ +
    |fderiv ℝ R x v| * (‖e₁ x‖ + ‖e₂ x‖) +
      |R x| * (‖fderiv ℝ e₁ x v‖ + ‖fderiv ℝ e₂ x v‖)
  have hL : Continuous L :=
    (hDQ.norm.add (hDR.abs.mul (h₁.continuous.norm.add h₂.continuous.norm))).add
      (hR.continuous.abs.mul (hD₁.norm.add hD₂.norm))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hL.continuousOn
  refine ⟨max 0 C, le_max_left _ _, fun α x hx => ?_⟩
  exact (spatialError_bound Q R e₁ e₂ α x v).trans
    ((le_abs_self (L x)).trans ((hC x hx).trans (le_max_right _ _)))

theorem compact_spatialError_bound_on {Q : E → Vec} {R : E → ℝ} {e₁ e₂ : E → Vec}
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hQ : ContDiffOn ℝ ∞ Q U) (hR : ContDiffOn ℝ ∞ R U)
    (h₁ : ContDiffOn ℝ ∞ e₁ U) (h₂ : ContDiffOn ℝ ∞ e₂ U) (v : E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : E → ℝ) x, x ∈ K →
      ‖spatialError Q R e₁ e₂ α x v‖ ≤ C := by
  have hDQ : ContinuousOn (fun x => fderiv ℝ Q x v) U :=
    ((hQ.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn
  have hDR : ContinuousOn (fun x => fderiv ℝ R x v) U :=
    ((hR.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn
  have hD₁ : ContinuousOn (fun x => fderiv ℝ e₁ x v) U :=
    ((h₁.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn
  have hD₂ : ContinuousOn (fun x => fderiv ℝ e₂ x v) U :=
    ((h₂.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn
  let L : E → ℝ := fun x => ‖fderiv ℝ Q x v‖ +
    |fderiv ℝ R x v| * (‖e₁ x‖ + ‖e₂ x‖) +
      |R x| * (‖fderiv ℝ e₁ x v‖ + ‖fderiv ℝ e₂ x v‖)
  have hL : ContinuousOn L U :=
    (hDQ.norm.add (hDR.abs.mul (h₁.continuousOn.norm.add h₂.continuousOn.norm))).add
      (hR.continuousOn.abs.mul (hD₁.norm.add hD₂.norm))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hL.mono hKU)
  refine ⟨max 0 C, le_max_left _ _, fun α x hx => ?_⟩
  exact (spatialError_bound Q R e₁ e₂ α x v).trans
    ((le_abs_self (L x)).trans ((hC x hx).trans (le_max_right _ _)))

/-- The true differentiated velocity has the first normal bound, with no angular derivative. -/
theorem circular_first_normal_bound {Q : E → Vec} {R : E → ℝ}
    {e₁ e₂ : E → Vec} {α : E → ℝ} {x v : E} {n : Vec}
    (hQ : DifferentiableAt ℝ Q x) (hR : DifferentiableAt ℝ R x)
    (h₁ : DifferentiableAt ℝ e₁ x) (h₂ : DifferentiableAt ℝ e₂ x)
    (hα : DifferentiableAt ℝ α x) (hn : n ⬝ᵥ n = 1)
    (horth : angularDirection (e₁ x) (e₂ x) (α x) ⬝ᵥ n = 0) :
    |fderiv ℝ (fun y => Q y + R y • direction (e₁ y) (e₂ y) (α y)) x v ⬝ᵥ n| ≤
      4 * ‖spatialError Q R e₁ e₂ α x v‖ := by
  rw [circular_velocity_derivative hQ hR h₁ h₂ hα]
  exact first_normal_bound hn horth _ _

/-- The other normal coefficient is `R` times the angular derivative plus the same bounded error. -/
theorem circular_second_normal_bound {Q : E → Vec} {R : E → ℝ}
    {e₁ e₂ : E → Vec} {α : E → ℝ} {x v : E}
    (hQ : DifferentiableAt ℝ Q x) (hR : DifferentiableAt ℝ R x)
    (h₁ : DifferentiableAt ℝ e₁ x) (h₂ : DifferentiableAt ℝ e₂ x)
    (hα : DifferentiableAt ℝ α x)
    (hunit : angularDirection (e₁ x) (e₂ x) (α x) ⬝ᵥ
      angularDirection (e₁ x) (e₂ x) (α x) = 1) :
    |fderiv ℝ (fun y => Q y + R y • direction (e₁ y) (e₂ y) (α y)) x v ⬝ᵥ
      angularDirection (e₁ x) (e₂ x) (α x) - R x * fderiv ℝ α x v| ≤
      4 * ‖spatialError Q R e₁ e₂ α x v‖ := by
  rw [circular_velocity_derivative hQ hR h₁ h₂ hα]
  exact second_normal_error_bound hunit _ _

end ClosedSurfaceR4.VelocityFrame

end

end OAI
