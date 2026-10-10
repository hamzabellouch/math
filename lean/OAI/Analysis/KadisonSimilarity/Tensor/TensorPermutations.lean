import OAI.Analysis.KadisonSimilarity.Tensor.TensorWords
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI

/-!
# Permutations of completed Hilbert tensor words

The permutation maps are constructed from the multilinear universal property
and proved isometric on the algebraic tensor power before completion.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem tensorWord_update_add : ∀ n : ℕ, ∀ (x : Fin n → E) (i : Fin n) (a b : E),
    tensorWord (Function.update x i (a + b)) =
      tensorWord (Function.update x i a) + tensorWord (Function.update x i b) := by
  intro n
  induction n with
  | zero => intro _ i; exact Fin.elim0 i
  | succ n ih =>
      intro x i a b
      cases i using Fin.cases with
      | zero =>
          change (a + b) ⊗ₜ[ℂ] tensorWord (Fin.tail (Function.update x 0 (a + b))) =
            a ⊗ₜ[ℂ] tensorWord (Fin.tail (Function.update x 0 a)) +
              b ⊗ₜ[ℂ] tensorWord (Fin.tail (Function.update x 0 b))
          simp only [Fin.tail_update_zero, TensorProduct.add_tmul]
      | succ i =>
          change Function.update x i.succ (a + b) 0 ⊗ₜ[ℂ]
            tensorWord (Fin.tail (Function.update x i.succ (a + b))) =
            Function.update x i.succ a 0 ⊗ₜ[ℂ] tensorWord (Fin.tail (Function.update x i.succ a)) +
              Function.update x i.succ b 0 ⊗ₜ[ℂ] tensorWord (Fin.tail (Function.update x i.succ b))
          simp only [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i)),
            Fin.tail_update_succ, ih, TensorProduct.tmul_add]

private theorem tensorWord_update_smul : ∀ n : ℕ, ∀ (x : Fin n → E) (i : Fin n) (c : ℂ) (a : E),
    tensorWord (Function.update x i (c • a)) = c • tensorWord (Function.update x i a) := by
  intro n
  induction n with
  | zero => intro _ i; exact Fin.elim0 i
  | succ n ih =>
      intro x i c a
      cases i using Fin.cases with
      | zero =>
          change (c • a) ⊗ₜ[ℂ] tensorWord (Fin.tail (Function.update x 0 (c • a))) =
            c • (a ⊗ₜ[ℂ] tensorWord (Fin.tail (Function.update x 0 a)))
          simp only [Fin.tail_update_zero, TensorProduct.smul_tmul']
      | succ i =>
          change Function.update x i.succ (c • a) 0 ⊗ₜ[ℂ]
            tensorWord (Fin.tail (Function.update x i.succ (c • a))) =
              c • (Function.update x i.succ a 0 ⊗ₜ[ℂ]
                tensorWord (Fin.tail (Function.update x i.succ a)))
          simp only [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i)),
            Fin.tail_update_succ, ih, TensorProduct.tmul_smul]

/-- The elementary word map, with its multilinearity bundled. -/
def tensorWordMultilinear (n : ℕ) : MultilinearMap ℂ (fun _ : Fin n => E) (TensorWord E n) :=
  MultilinearMap.mk' tensorWord (tensorWord_update_add n) (tensorWord_update_smul n)

@[simp] theorem tensorWordMultilinear_apply (n : ℕ) (x : Fin n → E) :
    tensorWordMultilinear n x = tensorWord x := rfl

variable (E)

/-- The multilinear universal property of the iterated algebraic tensor word. -/
def tensorWordLiftLinear (F : Type*) [AddCommGroup F] [Module ℂ F] :
    (n : ℕ) → MultilinearMap ℂ (fun _ : Fin n => E) F →ₗ[ℂ] (TensorWord E n →ₗ[ℂ] F)
  | 0 =>
    { toFun := fun f =>
        { toFun := fun z => z.down • f Fin.elim0
          map_add' := fun _ _ => add_smul _ _ _
          map_smul' := fun c z => mul_smul c z.down _ }
      map_add' := by intro f g; ext z; exact smul_add _ _ _
      map_smul' := by intro c f; ext z; exact smul_comm _ _ _ }
  | n + 1 =>
    { toFun := fun f => TensorProduct.lift ((tensorWordLiftLinear F n).comp f.curryLeft)
      map_add' := by
        intro f g
        apply TensorProduct.ext'
        intro a b
        change tensorWordLiftLinear F n ((f + g).curryLeft a) b = _
        have heq : (f + g).curryLeft a = f.curryLeft a + g.curryLeft a := rfl
        rw [heq, map_add, LinearMap.add_apply]
        rfl
      map_smul' := by
        intro c f
        apply TensorProduct.ext'
        intro a b
        change tensorWordLiftLinear F n ((c • f).curryLeft a) b = _
        have heq : (c • f).curryLeft a = c • f.curryLeft a := rfl
        rw [heq, map_smul, LinearMap.smul_apply]
        rfl }

variable {E}

@[simp] theorem tensorWordLiftLinear_apply_word {F : Type*} [AddCommGroup F] [Module ℂ F] :
    ∀ (n : ℕ) (f : MultilinearMap ℂ (fun _ : Fin n => E) F) (x : Fin n → E),
      tensorWordLiftLinear E F n f (tensorWord x) = f x := by
  intro n
  induction n with
  | zero =>
      intro f x
      change (1 : ℂ) • f Fin.elim0 = f x
      have hx : x = Fin.elim0 := Subsingleton.elim _ _
      rw [hx, one_smul]
  | succ n ih =>
      intro f x
      change tensorWordLiftLinear E F n (f.curryLeft (x 0)) (tensorWord (Fin.tail x)) = f x
      rw [ih, MultilinearMap.curryLeft_apply, Fin.cons_self_tail]

/-- Algebraic linear maps on tensor words are determined by elementary words. -/
theorem linearMap_ext_tensorWords {F : Type*} [AddCommGroup F] [Module ℂ F] {n : ℕ}
    (f g : TensorWord E n →ₗ[ℂ] F)
    (hword : ∀ x : Fin n → E, f (tensorWord x) = g (tensorWord x)) : f = g := by
  let S : Submodule ℂ (TensorWord E n) := (f - g).ker
  have hmem (z : TensorWord E n) : z ∈ S :=
    tensorWord_mem_submodule n S (fun x => sub_eq_zero.mpr (hword x)) z
  ext z
  exact sub_eq_zero.mp (hmem z)

/-- The algebraic map permuting tensor positions. -/
def tensorPermutationLinear {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    TensorWord E n →ₗ[ℂ] TensorWord E n :=
  tensorWordLiftLinear E (TensorWord E n) n ((tensorWordMultilinear n).domDomCongr σ.symm)

@[simp] theorem tensorPermutationLinear_word {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Fin n → E) :
    tensorPermutationLinear σ (tensorWord x) = tensorWord (fun i => x (σ.symm i)) := by
  rw [tensorPermutationLinear, tensorWordLiftLinear_apply_word]
  rfl

private theorem linearMap_preserves_inner_of_words {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] {n : ℕ}
    (f : TensorWord E n →ₗ[ℂ] F)
    (hword : ∀ x y : Fin n → E,
      inner ℂ (f (tensorWord x)) (f (tensorWord y)) = inner ℂ (tensorWord x) (tensorWord y)) :
    ∀ a b, inner ℂ (f a) (f b) = inner ℂ a b := by
  have hfirst (x : Fin n → E) (b : TensorWord E n) :
      inner ℂ (f (tensorWord x)) (f b) = inner ℂ (tensorWord x) b := by
    have heq := linearMap_ext_tensorWords
      ((innerSL ℂ (f (tensorWord x))).toLinearMap.comp f)
      (innerSL ℂ (tensorWord x)).toLinearMap (hword x)
    exact congrArg (fun g : TensorWord E n →ₗ[ℂ] ℂ => g b) heq
  intro a b
  have heq := linearMap_ext_tensorWords ((innerSL ℂ (f a)).toLinearMap.comp f)
    (innerSL ℂ a).toLinearMap (fun x => by
      change inner ℂ (f a) (f (tensorWord x)) = inner ℂ a (tensorWord x)
      simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) (hfirst x a))
  exact congrArg (fun g : TensorWord E n →ₗ[ℂ] ℂ => g b) heq

/-- Tensor-position permutations preserve the Hilbert inner product. -/
def tensorPermutationIsometry {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    TensorWord E n →ₗᵢ[ℂ] TensorWord E n :=
  (tensorPermutationLinear σ).isometryOfInner (linearMap_preserves_inner_of_words _ (by
    intro x y
    simp only [tensorPermutationLinear_word, inner_tensorWord]
    exact Equiv.prod_comp σ.symm (fun i => inner ℂ (x i) (y i))))

/-- The corresponding permutation on the completed Hilbert tensor power. -/
def completedTensorPermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    CompletedTensorWord E n →ₗᵢ[ℂ] CompletedTensorWord E n :=
  (tensorPermutationIsometry σ).completion

@[simp] theorem completedTensorPermutation_word {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Fin n → E) :
    completedTensorPermutation σ (completedTensorWord x) =
      completedTensorWord (fun i => x (σ.symm i)) := by
  change (tensorPermutationIsometry σ).completion
    (tensorWord x : CompletedTensorWord E n) = _
  rw [LinearIsometry.completion_apply_coe]
  change (tensorPermutationLinear σ (tensorWord x) : CompletedTensorWord E n) = _
  rw [tensorPermutationLinear_word]
  rfl

theorem completedTensorPermutation_inverse {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (completedTensorPermutation σ.symm).toContinuousLinearMap.comp
      (completedTensorPermutation σ).toContinuousLinearMap =
        ContinuousLinearMap.id ℂ (CompletedTensorWord E n) := by
  apply continuousLinearMap_ext_completedTensorWords
  intro x
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    completedTensorPermutation_word, Equiv.symm_symm, Equiv.symm_apply_apply,
    ContinuousLinearMap.id_apply]

/-- Every tensor-position permutation fixes a repeated-letter tensor. -/
@[simp] theorem completedTensorPermutation_constant {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (x : E) :
    completedTensorPermutation σ (completedTensorWord (fun _ : Fin n => x)) =
      completedTensorWord (fun _ : Fin n => x) := by
  rw [completedTensorPermutation_word]

end KadisonSimilarity

end

end OAI
