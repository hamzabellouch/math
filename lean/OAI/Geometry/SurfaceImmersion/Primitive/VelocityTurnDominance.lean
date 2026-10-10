import OAI.Geometry.SurfaceImmersion.Primitive.VelocitySpatialBounds

namespace OAI

/-! A large spatial angular derivative gives the required strict lower bound
for the actual complementary normal component of the circular velocity. -/
noncomputable section
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem circular_turn_dominates {Q : E → Vec} {R : E → ℝ}
    {e₁ e₂ : E → Vec} {α : E → ℝ} {x v : E} {r C T : ℝ}
    (hQ : DifferentiableAt ℝ Q x) (hR : DifferentiableAt ℝ R x)
    (h₁ : DifferentiableAt ℝ e₁ x) (h₂ : DifferentiableAt ℝ e₂ x)
    (hα : DifferentiableAt ℝ α x)
    (hunit : angularDirection (e₁ x) (e₂ x) (α x) ⬝ᵥ
      angularDirection (e₁ x) (e₂ x) (α x) = 1)
    (hr : 0 < r) (hRx : r ≤ R x) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hbound : ‖spatialError Q R e₁ e₂ α x v‖ ≤ C)
    (hlarge : (T + 4 * C + 1) / r < fderiv ℝ α x v) :
    T + 1 < fderiv ℝ (fun y => Q y + R y • direction (e₁ y) (e₂ y) (α y)) x v ⬝ᵥ
      angularDirection (e₁ x) (e₂ x) (α x) := by
  have herr := circular_second_normal_bound (v := v) hQ hR h₁ h₂ hα hunit
  have hE := abs_le.mp (herr.trans (mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 4)))
  have hprod : T + 4 * C + 1 < r * fderiv ℝ α x v := by
    have hd := (div_lt_iff₀ hr).mp hlarge
    nlinarith
  have hdpos : 0 < fderiv ℝ α x v := by
    have hpos : 0 < (T + 4 * C + 1) / r := div_pos (by linarith) hr
    exact hpos.trans hlarge
  have hscale := mul_le_mul_of_nonneg_right hRx hdpos.le
  linarith [hE.1]

end ClosedSurfaceR4.VelocityFrame

end

end OAI
