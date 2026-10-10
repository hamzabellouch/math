import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.SliceEuclideanGenerator

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev State (α : Type*) [Fintype α] (q : ℕ) :=
  ↥((Finset.univ : Finset α).powersetCard q)

def relabel (q : ℕ) (e : Equiv.Perm α) : Equiv.Perm (State α q) where
  toFun S := ⟨S.val.image e, by
    have hc := (Finset.mem_powersetCard.mp S.property).2
    simp [Finset.mem_powersetCard, Finset.card_image_of_injective _ e.injective, hc]⟩
  invFun S := ⟨S.val.image e.symm, by
    have hc := (Finset.mem_powersetCard.mp S.property).2
    simp [Finset.mem_powersetCard, Finset.card_image_of_injective _ e.symm.injective, hc]⟩
  left_inv S := by apply Subtype.ext; simp [Finset.image_image]
  right_inv S := by apply Subtype.ext; simp [Finset.image_image]

@[simp] theorem relabel_val (q : ℕ) (e : Equiv.Perm α) (S : State α q) :
    (relabel q e S).val = S.val.image e := rfl

def swapState (q : ℕ) (a b : α) : Equiv.Perm (State α q) :=
  relabel q (Equiv.swap a b)

@[simp] theorem swapState_twice (q : ℕ) (a b : α) (S : State α q) :
    swapState q a b (swapState q a b S) = S := by
  apply Subtype.ext
  simp [swapState, Finset.image_image, Function.comp_def]

def moveOperator (q : ℕ) (a b : α) :
    EuclideanSpace ℝ (State α q) →ₗ[ℝ] EuclideanSpace ℝ (State α q) where
  toFun f := WithLp.toLp 2 (fun S => f (swapState q a b S))
  map_add' _ _ := by ext S; rfl
  map_smul' _ _ := by ext S; rfl

@[simp] theorem moveOperator_apply (q : ℕ) (a b : α)
    (f : EuclideanSpace ℝ (State α q)) (S : State α q) :
    moveOperator q a b f S = f (swapState q a b S) := rfl

@[simp] theorem moveOperator_twice (q : ℕ) (a b : α)
    (f : EuclideanSpace ℝ (State α q)) :
    moveOperator q a b (moveOperator q a b f) = f := by
  ext S
  simp

theorem moveOperator_symmetric (q : ℕ) (a b : α) :
    (moveOperator q a b).IsSymmetric := by
  intro f g
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, moveOperator_apply]
  have h := Equiv.sum_comp (swapState q a b)
    (fun S : State α q => g S * f (swapState q a b S))
  simpa only [swapState_twice] using h.symm

theorem move_energy (q : ℕ) (a b : α) (f : EuclideanSpace ℝ (State α q)) :
    ⟪f, f - moveOperator q a b f⟫ =
      (1 / 2 : ℝ) * ‖f - moveOperator q a b f‖ ^ 2 := by
  have hs := moveOperator_symmetric q a b f (moveOperator q a b f)
  rw [moveOperator_twice] at hs
  have hn := norm_sub_sq_real f (moveOperator q a b f)
  have hnorm : ‖moveOperator q a b f‖ ^ 2 = ‖f‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using hs
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  rw [hn, hnorm]
  ring

def generator (q : ℕ) :
    EuclideanSpace ℝ (State α q) →ₗ[ℝ] EuclideanSpace ℝ (State α q) :=
  (1 / 4 : ℝ) • ∑ a : α, ∑ b : α, (LinearMap.id - moveOperator q a b)

@[simp] theorem generator_apply (q : ℕ) (f : EuclideanSpace ℝ (State α q))
    (S : State α q) :
    generator q f S = (∑ a : α, ∑ b : α, (f S - f (swapState q a b S))) / 4 := by
  simp only [generator, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.sub_apply, LinearMap.id_apply, PiLp.smul_apply, smul_eq_mul,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.sub_apply, moveOperator_apply]
  ring

theorem generator_symmetric (q : ℕ) : (generator (α := α) q).IsSymmetric := by
  apply LinearMap.IsSymmetric.smul (by simp)
  apply LinearMap.isSymmetric_sum
  intro a _
  apply LinearMap.isSymmetric_sum
  intro b _
  exact LinearMap.IsSymmetric.id.sub (moveOperator_symmetric q a b)

theorem generator_energy (q : ℕ) (f : EuclideanSpace ℝ (State α q)) :
    ⟪f, generator q f⟫ =
      (1 / 8 : ℝ) * ∑ a : α, ∑ b : α, ‖f - moveOperator q a b f‖ ^ 2 := by
  simp only [generator, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.sub_apply, LinearMap.id_apply, inner_smul_right, inner_sum]
  simp_rw [move_energy, ← Finset.mul_sum]
  ring

theorem generator_positive (q : ℕ) (f : EuclideanSpace ℝ (State α q)) :
    0 ≤ ⟪f, generator q f⟫ := by
  rw [generator_energy]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _)

end Problem315.SliceEuclideanGenerator

end

end OAI
