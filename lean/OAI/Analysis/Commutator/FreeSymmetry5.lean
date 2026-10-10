import Mathlib
import OAI.Analysis.Commutator.TensorDevelopment

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.HilbertTensor

open UniformSpace

open scoped TensorProduct

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma inner_map_left_adjoint (a b : E →L[ℂ] E)
    (hab : ∀ x y, inner ℂ (a x) y = inner ℂ x (b y))
    (x y : Completion (E ⊗[ℂ] F)) :
    inner ℂ (map a (1 : F →L[ℂ] F) x) y =
      inner ℂ x (map b (1 : F →L[ℂ] F) y) := by
  induction x, y using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x y =>
    induction x using TensorProduct.inductionOn with
    | add x x' hx hx' =>
      simp only [Completion.coe_add, map_add, inner_add_left, hx, hx']
    | tmul x v =>
      induction y using TensorProduct.inductionOn with
      | add y y' hy hy' =>
        simp only [Completion.coe_add, map_add, inner_add_right, hy, hy']
      | tmul y w =>
        simp only [map_coe_tmul, one_apply_eq_self, Completion.inner_coe,
          TensorProduct.inner_tmul, hab]

end Kadison.HilbertTensor
end

end OAI
