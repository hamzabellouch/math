import OAI.Analysis.KLS.Model
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

namespace OAI

noncomputable section

open Set MeasureTheory InnerProductSpace
open scoped ContDiff

namespace LeanBlast.KLS

variable {n : ℕ} {f : Space n → ℝ}

theorem IsTestFunction.continuous (hf : IsTestFunction f) : Continuous f :=
  hf.1.continuous

theorem IsTestFunction.continuous_gradient (hf : IsTestFunction f) :
    Continuous (gradient f) := by
  exact (toDual ℝ (Space n)).symm.continuous.comp
    (hf.1.continuous_fderiv (by simp))

theorem IsTestFunction.hasCompactSupport_gradient (hf : IsTestFunction f) :
    HasCompactSupport (gradient f) := by
  exact (hf.2.fderiv ℝ).comp_left
    (g := (toDual ℝ (Space n)).symm) (by simp)

theorem IsTestFunction.integrable (hf : IsTestFunction f)
    (μ : Measure (Space n)) [IsFiniteMeasure μ] : Integrable f μ :=
  hf.continuous.integrable_of_hasCompactSupport hf.2

theorem IsTestFunction.integrable_sq (hf : IsTestFunction f)
    (μ : Measure (Space n)) [IsFiniteMeasure μ] :
    Integrable (fun x => (f x) ^ 2) μ := by
  have hsupport := HasCompactSupport.comp_left (f := f)
    (g := fun value : ℝ => value ^ 2) hf.2 (by simp)
  exact (hf.continuous.pow 2).integrable_of_hasCompactSupport hsupport

theorem IsTestFunction.integrable_gradient_sq (hf : IsTestFunction f)
    (μ : Measure (Space n)) [IsFiniteMeasure μ] :
    Integrable (fun x => ‖gradient f x‖ ^ 2) μ := by
  have hsupport := HasCompactSupport.comp_left (f := gradient f)
    (g := fun vector : Space n => ‖vector‖ ^ 2) hf.hasCompactSupport_gradient (by simp)
  exact (hf.continuous_gradient.norm.pow 2).integrable_of_hasCompactSupport hsupport

theorem IsTestFunction.integrable_centered_sq (hf : IsTestFunction f)
    (μ : Measure (Space n)) [IsFiniteMeasure μ] :
    Integrable (fun x => (f x - expectation μ f) ^ 2) μ := by
  have hi := ((hf.integrable_sq μ).sub
    ((hf.integrable μ).const_mul (2 * expectation μ f))).add
      (integrable_const ((expectation μ f) ^ 2))
  convert hi using 1
  ext x
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem variance_nonneg (μ : Measure (Space n)) (f : Space n → ℝ) :
    0 ≤ variance μ f :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem dirichletEnergy_nonneg (μ : Measure (Space n)) (f : Space n → ℝ) :
    0 ≤ dirichletEnergy μ f :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem norm_gradient_eq_norm_fderiv (f : Space n → ℝ) (x : Space n) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (toDual ℝ (Space n)).symm.norm_map _

end LeanBlast.KLS

end

end OAI
