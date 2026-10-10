import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ProjectionDerivative

namespace OAI

namespace ProjectionComparison

open Set MeasureTheory

variable {V E : Type*} [Fintype V]

lemma project_path_lipschitz (S : System V E) (b v₀ v₁ : V → ℝ) (hne : (feasible S b).Nonempty) (x : V) :
    LipschitzWith ‖v₁-v₀‖₊ (fun t : ℝ => project S b hne (fun y => v₀ y+t*(v₁ y-v₀ y)) x) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq,Real.dist_eq]
  apply projection_parameter_stability S b b _ _ _ _ (‖v₁-v₀‖*|s-t|) (mul_nonneg (norm_nonneg _) (abs_nonneg _))
    (project_spec S b hne _) (project_spec S b hne _)
  · intro y hy;simpa using mul_nonneg (norm_nonneg (v₁-v₀)) (abs_nonneg (s-t))
  · intro y hy
    have hn : |v₁ y-v₀ y|≤‖v₁-v₀‖ := by simpa only [Real.norm_eq_abs,Pi.sub_apply] using norm_le_pi_norm (v₁-v₀) y
    calc
      |(v₀ y+s*(v₁ y-v₀ y))-(v₀ y+t*(v₁ y-v₀ y))|=|s-t| * |v₁ y-v₀ y| := by rw [← abs_mul];congr 1;ring
      _ ≤ ‖v₁-v₀‖*|s-t| := by nlinarith [abs_nonneg (s-t)]

lemma project_path_ae_derivative (S : System V E) (b v₀ v₁ : V → ℝ) (hne : (feasible S b).Nonempty) :
    ∀ᵐ t : ℝ,∀ x,DifferentiableAt ℝ (fun s => project S b hne (fun y => v₀ y+s*(v₁ y-v₀ y)) x) t := by
  apply MeasureTheory.ae_all_iff.mpr
  intro x
  exact (project_path_lipschitz S b v₀ v₁ hne x).ae_differentiableAt_real

end ProjectionComparison

end OAI
