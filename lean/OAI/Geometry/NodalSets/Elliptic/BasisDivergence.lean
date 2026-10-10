import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Tactic.Ring

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma constant_matrix_flux_derivative (D : Matrix n n ℝ) (F : n → E → ℝ)
    {x : E} (hF : ∀ a, DifferentiableAt ℝ (F a) x) (i : n) (v : E) :
    fderiv ℝ (fun y ↦ ∑ a, D i a * F a y) x v =
      ∑ a, D i a * fderiv ℝ (F a) x v := by
  rw [show (fun y ↦ ∑ a, D i a * F a y) =
    ∑ a, (fun y ↦ D i a * F a y) by ext y; simp]
  rw [fderiv_sum (fun a _ ↦ (hF a).const_mul (D i a))]
  simp only [_root_.sum_apply,fderiv_const_mul (hF _) _,
    _root_.smul_apply,smul_eq_mul]

omit [DecidableEq n] in
lemma basis_divergence_change (b c : Module.Basis n ℝ E) (F : n → E → ℝ)
    {x : E} (hF : ∀ a, DifferentiableAt ℝ (F a) x) :
    ∑ i, fderiv ℝ (fun y ↦ ∑ a, c.toMatrix b i a * F a y) x (c i) =
      ∑ a, fderiv ℝ (F a) x (b a) := by
  simp_rw [constant_matrix_flux_derivative _ F hF]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  conv_rhs => rw [← c.sum_toMatrix_smul_self b a]
  simp only [map_sum,map_smul,smul_eq_mul]

end
end Yau.Geometry

end OAI
