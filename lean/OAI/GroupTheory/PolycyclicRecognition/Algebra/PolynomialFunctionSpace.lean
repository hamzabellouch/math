import OAI.GroupTheory.PolycyclicRecognition.Geometry.FiniteCoordinateSmoothness
import Mathlib.Algebra.Polynomial.Eval.SMul

namespace OAI

/-! # The space of real polynomial functions -/

noncomputable section
namespace PolycyclicRecognition

def polynomialEvaluationLinear : Polynomial ℝ →ₗ[ℝ] (ℝ → ℝ) where
  toFun p t := p.eval t
  map_add' p q := by ext t; exact Polynomial.eval_add
  map_smul' a p := by ext t; exact Polynomial.eval_smul a p t

def polynomialFunctions : Submodule ℝ (ℝ → ℝ) := polynomialEvaluationLinear.range

theorem mem_polynomialFunctions_iff {f : ℝ → ℝ} :
    f ∈ polynomialFunctions ↔ ∃ p : Polynomial ℝ, ∀ t, p.eval t = f t := by
  change (∃ p, polynomialEvaluationLinear p = f) ↔ _
  simp only [funext_iff]
  rfl

theorem polynomialFunctions_const (a : ℝ) : (fun _ : ℝ => a) ∈ polynomialFunctions :=
  mem_polynomialFunctions_iff.mpr ⟨Polynomial.C a, fun _ => Polynomial.eval_C⟩

theorem polynomialFunctions_linear (a : ℝ) : (fun t : ℝ => t * a) ∈ polynomialFunctions :=
  mem_polynomialFunctions_iff.mpr ⟨Polynomial.X * Polynomial.C a, by
    intro t
    rw [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]⟩

variable {G V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem polynomial_of_coordinateEvaluations (e : V →ₗ[ℝ] (G → ℝ))
    (he : Function.Injective e) (F : ℝ → V)
    (hF : ∀ g, (fun t => e (F t) g) ∈ polynomialFunctions)
    (f : Module.Dual ℝ V) : (fun t => f (F t)) ∈ polynomialFunctions := by
  have hf : f ∈ Submodule.span ℝ (Set.range (coordinateEvaluation e)) := by
    rw [span_coordinateEvaluation e he]
    trivial
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, rfl⟩ := hf
    exact hF g
  | zero => exact polynomialFunctions.zero_mem
  | add f g _ _ hf hg => exact polynomialFunctions.add_mem hf hg
  | smul a f _ hf => exact polynomialFunctions.smul_mem a hf

end PolycyclicRecognition

end

end OAI
