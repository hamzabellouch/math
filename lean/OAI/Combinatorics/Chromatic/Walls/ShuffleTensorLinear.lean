import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.QuotientAlg

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def shuffleTensorLinear (a : I → I → ℕ) (d e : I → ℕ) :
    S d ⊗[ℚ] S e →ₗ[ℚ] S (d+e) := TensorProduct.lift (shuffleLinear a d e)

@[simp] lemma shuffleTensorLinear_tmul (a : I → I → ℕ) (d e : I → ℕ) (f : S d) (g : S e) :
    shuffleTensorLinear a d e (f ⊗ₜ[ℚ] g) = shufflePolynomial a f g := rfl

lemma tensorShuffle_tensorValue (a : I → I → ℕ) (d e : I → ℕ) (f : S d ⊗[ℚ] S e) :
    tensorShuffle a (tensorValue d e f) = localizeS (d+e) (shuffleTensorLinear a d e f) := by
  induction f using TensorProduct.inductionOn with
  | tmul f g =>
    rw [tensorValue_tmul,tensorShuffle_decomposable,shuffleTensorLinear_tmul]
    exact (shufflePolynomial_eq a f g).symm
  | add f g hf hg => simp only [map_add,hf,hg]

lemma invariant_transfer_eq (a : I → I → ℕ) (d e : I → ℕ)
    (p : MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ)
    (hp : ∀ σ,rename (sumAction (packAction (fun i=>Fin (d i)))
      (packAction (fun i=>Fin (e i))) σ) p = p) :
    tensorShuffle a p = localizeS (d+e) (shuffleTensorLinear a d e (separateTensor d e p)) := by
  rw [← tensorShuffle_tensorValue,tensorValue_separateTensor d e p hp]

lemma shuffleTensorLinear_mem (a : I → I → ℕ) (d e : I → ℕ) (f : S d ⊗[ℚ] S e) :
    shuffleTensorLinear a d e f ∈ shuffleImage a d e := by
  induction f using TensorProduct.inductionOn with
  | tmul f g => exact Submodule.subset_span ⟨f,g,rfl⟩
  | add f g hf hg => simpa only [map_add] using (shuffleImage a d e).add_mem hf hg

noncomputable def twoTargetTransfer (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    (S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂) →ₗ[ℚ]
      S (d₁+e₁) ⊗[ℚ] S (d₂+e₂) :=
  TensorProduct.map (shuffleTensorLinear a d₁ e₁) (shuffleTensorLinear a d₂ e₂)

@[simp] lemma twoTargetTransfer_tmul (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f₁ : S d₁) (g₁ : S e₁) (f₂ : S d₂) (g₂ : S e₂) :
    twoTargetTransfer a d₁ e₁ d₂ e₂ ((f₁ ⊗ₜ[ℚ] g₁) ⊗ₜ[ℚ] (f₂ ⊗ₜ[ℚ] g₂)) =
      shufflePolynomial a f₁ g₁ ⊗ₜ[ℚ] shufflePolynomial a f₂ g₂ := by
  simp [twoTargetTransfer]

lemma shuffleImage_le_destabilizing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d e : I → ℕ) (hd : d≠0) (he : e≠0) (hμ : μ d > μ (d+e)) :
    shuffleImage a d e ≤ destabilizingSpace a μ (d+e) := by
  apply Submodule.span_le.mpr
  rintro p ⟨f,g,rfl⟩
  exact Submodule.subset_span ⟨d,e,rfl,f,g,hd,he,hμ,rfl⟩

lemma quotient_shuffleTensorLinear_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d e : I → ℕ) (hd : d≠0) (he : e≠0) (hμ : μ d > μ (d+e))
    (f : S d ⊗[ℚ] S e) : quotientAlg a μ (d+e) (shuffleTensorLinear a d e f) = 0 := by
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    ((shuffleImage_le_destabilizing a μ d e hd he hμ) (shuffleTensorLinear_mem a d e f))

lemma quotient_twoTargetTransfer_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (h : (d₁≠0 ∧ e₁≠0 ∧ μ d₁ > μ (d₁+e₁)) ∨
         (d₂≠0 ∧ e₂≠0 ∧ μ d₂ > μ (d₂+e₂)))
    (f : (S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂)) :
    quotientTensor a μ (d₁+e₁) (d₂+e₂) (twoTargetTransfer a d₁ e₁ d₂ e₂ f) = 0 := by
  induction f using TensorProduct.inductionOn with
  | tmul f g =>
    simp only [twoTargetTransfer, TensorProduct.map_tmul, quotientTensor,
      Algebra.TensorProduct.map_tmul]
    rcases h with ⟨hd,he,hμ⟩ | ⟨hd,he,hμ⟩
    · rw [quotient_shuffleTensorLinear_zero a μ d₁ e₁ hd he hμ,TensorProduct.zero_tmul]
    · rw [quotient_shuffleTensorLinear_zero a μ d₂ e₂ hd he hμ,TensorProduct.tmul_zero]
  | add f g hf hg =>
    change (quotientTensor a μ (d₁+e₁) (d₂+e₂)).toLinearMap (twoTargetTransfer a d₁ e₁ d₂ e₂ (f+g)) = 0
    rw [(twoTargetTransfer a d₁ e₁ d₂ e₂).map_add, (quotientTensor a μ (d₁+e₁) (d₂+e₂)).toLinearMap.map_add]
    exact (congrArg₂ (· + ·) hf hg).trans (add_zero 0)

end ElementaryPositivity.RawShuffle

end

end OAI
