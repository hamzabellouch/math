import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianDomination

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section UniformBounds
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_le_of_fderiv_bound (f : E → ℝ) (hd : Differentiable ℝ f)
    (C : ℝ) (hC : ∀ x, ‖fderiv ℝ f x‖ ≤ C) (x : E) :
    ‖f x‖ ≤ ‖f 0‖ + C*‖x‖ := by
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x (_ : x ∈ (Set.univ : Set E)) => hd x)
    (fun x (_ : x ∈ (Set.univ : Set E)) => hC x) convex_univ
    (mem_univ (0:E)) (mem_univ x)
  simp only [sub_zero] at h
  calc
    ‖f x‖ = ‖(f x-f 0)+f 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖f x-f 0‖+‖f 0‖ := norm_add_le _ _
    _ ≤ ‖f 0‖+C*‖x‖ := by linarith

theorem exp_mul_growth_of_fderiv_bound (f : E → ℝ) (hd : Differentiable ℝ f)
    (C : ℝ) (hC₀ : 0 ≤ C) (hC : ∀ x, ‖fderiv ℝ f x‖ ≤ C) (m : ℝ) :
    HasExpGrowth (fun x => Real.exp (m*f x)) := by
  refine ⟨Real.exp (|m| *‖f 0‖), |m| *C, (Real.exp_pos _).le,
    mul_nonneg (abs_nonneg _) hC₀, ?_⟩
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hf := norm_le_of_fderiv_bound f hd C hC x
  have hb : m*f x ≤ |m| *‖f x‖ := by
    simpa only [Real.norm_eq_abs, abs_mul] using le_abs_self (m*f x)
  nlinarith [mul_le_mul_of_nonneg_left hf (abs_nonneg m)]

def positiveGaussianLogStep (m : ℝ) (f : E × ℝ → ℝ) (x : E) : ℝ :=
  Real.log (∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1) / m

theorem positiveGaussianLogStep_partition_pos (f : E × ℝ → ℝ)
    (hd : Differentiable ℝ f) (C : ℝ) (hC₀ : 0 ≤ C)
    (hC : ∀ x, ‖fderiv ℝ f x‖ ≤ C) (m : ℝ) (x : E) :
    0 < ∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1 := by
  apply integral_exp_pos
  exact (exp_mul_growth_of_fderiv_bound f hd C hC₀ hC m).integrable_gaussian_section
    (Real.continuous_exp.comp (continuous_const.mul hd.continuous)) x

end UniformBounds
end SK.Analytic

end
end
end
end
end
end

end OAI
