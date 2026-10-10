import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteLabelReflection
import Mathlib.Analysis.Normed.Module.Basic

namespace OAI

/-! # Affine agreement on a facet determines the tangential linear part -/

namespace PolycyclicRecognition

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [AddCommGroup V] [Module ℝ V]

/-- Agreement on a relative neighborhood of a facet point implies agreement
of linear parts on the entire parallel hyperplane. -/
theorem linear_eq_on_kernel_of_affine_facet_agreement
    (A C : W →ₗ[ℝ] V) (b₁ b₂ : V) (ℓ : W →ₗ[ℝ] ℝ)
    (p : W) {ρ : ℝ} (hρ : 0 < ρ)
    (hagree : ∀ q, ℓ q = ℓ p → ‖q - p‖ < ρ → A q + b₁ = C q + b₂) :
    ∀ w, ℓ w = 0 → A w = C w := by
  have hp := hagree p rfl (by simpa using hρ)
  intro w hw
  let t := ρ / (2 * (‖w‖ + 1))
  have ht : 0 < t := div_pos hρ (by positivity)
  have htw : ‖t • w‖ < ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp only [t]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (‖w‖ + 1))).mpr
    nlinarith [norm_nonneg w]
  have he := hagree (p + t • w) (by simp [hw]) (by simpa using htw)
  simp only [map_add, map_smul] at he
  have he' : t • A w = t • C w := by
    calc
      t • A w = (A p + t • A w + b₁) - (A p + b₁) := by abel
      _ = (C p + t • C w + b₂) - (C p + b₂) := by rw [he, hp]
      _ = t • C w := by abel
  exact smul_right_injective _ ht.ne' he'

end PolycyclicRecognition

end OAI
