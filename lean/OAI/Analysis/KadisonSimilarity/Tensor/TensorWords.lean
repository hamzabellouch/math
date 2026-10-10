import OAI.Analysis.KadisonSimilarity.Tensor.TensorSlices
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Finite words in completed Hilbert tensor powers

The scalar word has length zero. Longer words are genuine Hilbert tensor
products, completed only after the finite algebraic tensor product is formed.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct
universe u

/-- Scalars at the same universe as the Hilbert space. -/
abbrev TensorScalars : Type u := ULift.{u} ℂ

instance tensorScalarsInnerProductSpace : InnerProductSpace ℂ (TensorScalars.{u}) where
  inner x y := inner ℂ x.down y.down
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner x.down
  conj_inner_symm x y := inner_conj_symm x.down y.down
  add_left x y z := inner_add_left x.down y.down z.down
  smul_left x y r := inner_smul_left x.down y.down r

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Bundling keeps the vector-space structures available during the recursion. -/
structure TensorWordSpace where
  Carrier : Type u
  normed : NormedAddCommGroup Carrier
  innerSpace : @InnerProductSpace ℂ Carrier _ normed.toSeminormedAddCommGroup

attribute [instance] TensorWordSpace.normed TensorWordSpace.innerSpace

/-- Right-associated algebraic Hilbert tensor powers, including degree zero. -/
def tensorWordSpace (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    ℕ → TensorWordSpace.{u}
  | 0 => ⟨TensorScalars, inferInstance, inferInstance⟩
  | n + 1 => ⟨E ⊗[ℂ] (tensorWordSpace E n).Carrier, inferInstance, inferInstance⟩

abbrev TensorWord (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (n : ℕ) :=
  (tensorWordSpace E n).Carrier

/-- The elementary word determined by its letters. -/
def tensorWord : {n : ℕ} → (Fin n → E) → TensorWord E n
  | 0, _ => ⟨1⟩
  | _n + 1, x => x 0 ⊗ₜ[ℂ] tensorWord (Fin.tail x)

/-- Inner products of words are products of the inner products of letters. -/
theorem inner_tensorWord {n : ℕ} (x y : Fin n → E) :
    inner ℂ (tensorWord x) (tensorWord y) = ∏ i, inner ℂ (x i) (y i) := by
  induction n with
  | zero =>
      change inner ℂ (1 : ℂ) 1 = _
      simp
  | succ n ih =>
      change inner ℂ (x 0 ⊗ₜ[ℂ] tensorWord (Fin.tail x))
        (y 0 ⊗ₜ[ℂ] tensorWord (Fin.tail y)) = _
      rw [TensorProduct.inner_tmul, ih, Fin.prod_univ_succ]
      rfl

/-- Completed finite Hilbert tensor powers. -/
abbrev CompletedTensorWord (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℕ) := UniformSpace.Completion (TensorWord E n)

/-- An elementary word in the completed tensor power. -/
def completedTensorWord {n : ℕ} (x : Fin n → E) : CompletedTensorWord E n := tensorWord x

@[simp] theorem inner_completedTensorWord {n : ℕ} (x y : Fin n → E) :
    inner ℂ (completedTensorWord x) (completedTensorWord y) = ∏ i, inner ℂ (x i) (y i) := by
  rw [completedTensorWord, completedTensorWord, UniformSpace.Completion.inner_coe,
    inner_tensorWord]

/-- All words formed from an orthonormal alphabet form an orthonormal family. -/
theorem orthonormal_completedTensorWords {J : Type*} (h : J → E) (hh : Orthonormal ℂ h)
    (n : ℕ) :
    Orthonormal ℂ (fun f : Fin n → J => completedTensorWord (fun i => h (f i))) := by
  classical
  rw [orthonormal_iff_ite]
  intro f g
  rw [inner_completedTensorWord]
  simp only [orthonormal_iff_ite.mp hh]
  by_cases hfg : f = g
  · subst g
    simp
  · have hex : ∃ i, f i ≠ g i := by
      by_contra! hc
      exact hfg (funext hc)
    obtain ⟨i, hi⟩ := hex
    simp only [hfg, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- The sum of a finite orthonormal family has norm the square root of its
cardinality. This supplies the exact growth rate in the pairing test. -/
theorem norm_sum_orthonormal {H J : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [Fintype J] (v : J → H) (hv : Orthonormal ℂ v) :
    ‖∑ j, v j‖ = Real.sqrt (Fintype.card J) := by
  classical
  have hi : inner ℂ (∑ j, v j) (∑ j, v j) = (Fintype.card J : ℂ) := by
    simp only [sum_inner, inner_sum, orthonormal_iff_ite.mp hv]
    simp
  have hs : ‖∑ j, v j‖ ^ 2 = (Fintype.card J : ℝ) := by
    rw [@norm_sq_eq_re_inner ℂ, hi]
    simp
  rw [← hs, Real.sqrt_sq_eq_abs, abs_norm]

/-- Elementary words linearly span the algebraic tensor power. -/
theorem tensorWord_mem_submodule : ∀ n : ℕ, ∀ S : Submodule ℂ (TensorWord E n),
    (∀ x : Fin n → E, tensorWord x ∈ S) → ∀ z, z ∈ S := by
  intro n
  induction n with
  | zero =>
      intro S hS z
      have heq : z = z.down • tensorWord (Fin.elim0 : Fin 0 → E) := by
        cases z
        apply ULift.ext
        change _ = _ * 1
        exact (mul_one _).symm
      rw [heq]
      exact S.smul_mem _ (hS _)
  | succ n ih =>
      intro S hS z
      induction z using TensorProduct.inductionOn with
      | tmul a b =>
          let T : Submodule ℂ (TensorWord E n) :=
            S.comap (TensorProduct.mk ℂ E (TensorWord E n) a)
          apply ih T ?_ b
          intro x
          change a ⊗ₜ[ℂ] tensorWord x ∈ S
          change tensorWord (Fin.cons a x) ∈ S
          exact hS _
      | add a b ha hb => exact S.add_mem ha hb

/-- Elementary words are total after Hilbert completion. -/
theorem completedTensorWord_mem_closed_submodule {n : ℕ}
    (S : Submodule ℂ (CompletedTensorWord E n))
    (hclosed : IsClosed (S : Set (CompletedTensorWord E n)))
    (hword : ∀ x : Fin n → E, completedTensorWord x ∈ S)
    (z : CompletedTensorWord E n) : z ∈ S := by
  refine UniformSpace.Completion.induction_on z hclosed ?_
  intro w
  let T : Submodule ℂ (TensorWord E n) :=
    S.comap (UniformSpace.Completion.toComplL : TensorWord E n →L[ℂ]
      CompletedTensorWord E n).toLinearMap
  exact tensorWord_mem_submodule n T hword w

/-- Continuous operators are determined by their values on elementary words. -/
theorem continuousLinearMap_ext_completedTensorWords {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] {n : ℕ}
    (f g : CompletedTensorWord E n →L[ℂ] F)
    (hword : ∀ x : Fin n → E, f (completedTensorWord x) = g (completedTensorWord x)) : f = g := by
  let S : Submodule ℂ (CompletedTensorWord E n) := (f - g).ker
  have hmem (z : CompletedTensorWord E n) : z ∈ S := by
    apply completedTensorWord_mem_closed_submodule S (f - g).isClosed_ker ?_ z
    intro x
    change f (completedTensorWord x) - g (completedTensorWord x) = 0
    exact sub_eq_zero.mpr (hword x)
  ext z
  exact sub_eq_zero.mp (hmem z)

/-- Vanishing simple-tensor coefficients force a completed tensor operator
to be zero. Both input and output totality are proved above. -/
theorem tensorOperator_eq_zero_of_word_coefficients {k l : ℕ}
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (hword : ∀ (x : Fin k → E) (y : Fin l → E),
      inner ℂ (completedTensorWord y) (Y (completedTensorWord x)) = 0) : Y = 0 := by
  apply continuousLinearMap_ext_completedTensorWords
  intro x
  have hlin : innerSL ℂ (Y (completedTensorWord x)) = 0 := by
    apply continuousLinearMap_ext_completedTensorWords
    intro y
    change inner ℂ (Y (completedTensorWord x)) (completedTensorWord y) = 0
    simpa only [inner_conj_symm, map_zero] using congrArg (starRingEnd ℂ) (hword x y)
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  have heq := congrArg (fun f : CompletedTensorWord E l →L[ℂ] ℂ =>
    f (Y (completedTensorWord x))) hlin
  change inner ℂ (Y (completedTensorWord x)) (Y (completedTensorWord x)) = 0 at heq
  exact heq

end KadisonSimilarity

end

end OAI
