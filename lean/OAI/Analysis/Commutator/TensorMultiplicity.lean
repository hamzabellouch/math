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

variable {E F J K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def pair (x : E) (a : J) : Completion (E ⊗[ℂ] J) := (x ⊗ₜ[ℂ] a : E ⊗[ℂ] J)

@[simp] lemma inner_pair (x y : E) (a b : J) :
    inner ℂ (pair x a) (pair y b) = inner ℂ x y * inner ℂ a b := by
  simp only [pair, Completion.inner_coe, TensorProduct.inner_tmul]

@[simp] lemma norm_pair (x : E) (a : J) : ‖pair x a‖ = ‖x‖ * ‖a‖ := by
  simp only [pair, Completion.norm_coe, TensorProduct.norm_tmul]

def insertRight (a : J) : E →L[ℂ] Completion (E ⊗[ℂ] J) :=
  Completion.toComplL.comp ((TensorProduct.mkL ℂ E J).flip a)

@[simp] lemma insertRight_apply (a : J) (x : E) : insertRight a x = pair x a := rfl

lemma norm_insertRight_le (a : J) : ‖insertRight (E := E) a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  simp only [insertRight_apply, norm_pair, mul_comm, le_refl]

def insertLeft (x : E) : J →L[ℂ] Completion (E ⊗[ℂ] J) :=
  Completion.toComplL.comp (TensorProduct.mkL ℂ E J x)

@[simp] lemma insertLeft_apply (x : E) (a : J) : insertLeft x a = pair x a := rfl

lemma norm_insertLeft_le (x : E) : ‖insertLeft (J := J) x‖ ≤ ‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro a
  simp only [insertLeft_apply, norm_pair, le_refl]

@[simp] lemma insertRight_adjoint_pair [CompleteSpace E] (b : J) (x : E) (a : J) :
    (insertRight b).adjoint (pair x a) = inner ℂ b a • x := by
  apply (ext_inner_left ℂ)
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right, insertRight_apply, inner_pair, inner_smul_right]
  exact mul_comm _ _

@[simp] lemma insertLeft_adjoint_pair [CompleteSpace J] (y : E) (x : E) (a : J) :
    (insertLeft y).adjoint (pair x a) = inner ℂ y x • a := by
  apply (ext_inner_left ℂ)
  intro b
  rw [ContinuousLinearMap.adjoint_inner_right, insertLeft_apply, inner_pair, inner_smul_right]

def scalarSlice [CompleteSpace F] (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (F ⊗[ℂ] K))
    (a : J) (b : K) : E →L[ℂ] F :=
  ((insertRight b).adjoint.comp T).comp (insertRight a)

lemma scalarSlice_inner [CompleteSpace F] (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (F ⊗[ℂ] K))
    (a : J) (b : K) (x : E) (y : F) :
    inner ℂ y (scalarSlice T a b x) = inner ℂ (pair y b) (T (pair x a)) := by
  simp only [scalarSlice, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, insertRight_apply]

lemma eq_zero_of_pair_inner (z : Completion (E ⊗[ℂ] J))
    (h : ∀ x a, inner ℂ (pair x a) z = 0) : z = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  have hz (y : Completion (E ⊗[ℂ] J)) : inner ℂ y z = 0 := by
    induction y using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) continuous_const
    | ih y =>
      induction y using TensorProduct.inductionOn with
      | tmul x a => exact h x a
      | add x y hx hy => simp only [Completion.coe_add, inner_add_left, hx, hy, add_zero]
  exact hz z

lemma pair_inner_ext (z w : Completion (E ⊗[ℂ] J))
    (h : ∀ x a, inner ℂ (pair x a) z = inner ℂ (pair x a) w) : z = w := by
  apply sub_eq_zero.mp
  apply eq_zero_of_pair_inner
  intro x a
  rw [inner_sub_right, h, sub_self]

lemma eq_zero_of_scalarSlice [CompleteSpace F]
    (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (F ⊗[ℂ] K))
    (h : ∀ a b, scalarSlice T a b = 0) : T = 0 := by
  apply completion_ext
  intro x a
  change T (pair x a) = 0
  apply eq_zero_of_pair_inner
  intro y b
  rw [← scalarSlice_inner, h, zero_apply, inner_zero_right]

end Kadison.HilbertTensor
end

end OAI
