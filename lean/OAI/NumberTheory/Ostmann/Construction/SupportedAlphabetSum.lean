import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleMap

namespace OAI

/-! # Exact alphabet restriction for the original independent priors -/
namespace Ostmann
open scoped Classical BigOperators

theorem finite_sum_embedding_support {A B M : Type*} [Fintype A] [Fintype B]
    [AddCommMonoid M] (e : B ↪ A) (f : A → M)
    (hf : ∀ a, a ∉ Set.range e → f a = 0) :
    (∑ a, f a) = ∑ b, f (e b) := by
  rw [← Finset.sum_image e.injective.injOn]
  apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro a _ ha
  apply hf a
  simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using ha

theorem productPrior_alphabet_sum {I A B : Type*} [Fintype I] [Fintype A] [Fintype B]
    (e : B ↪ A) (μ : I → A → ℝ) (F : (I → A) → ℂ)
    (hμ : ∀ i a, μ i a ≠ 0 → a ∈ Set.range e) :
    (∑ x : I → A, ((∏ i, μ i (x i) : ℝ) : ℂ) * F x) =
      ∑ y : I → B, ((∏ i, μ i (e (y i)) : ℝ) : ℂ) * F (e ∘ y) := by
  let E : (I → B) ↪ (I → A) :=
    ⟨fun y => e ∘ y, fun x y h => funext fun i => e.injective (congrFun h i)⟩
  apply finite_sum_embedding_support E
  intro x hx
  have hp : (∏ i, μ i (x i)) = 0 := by
    by_contra hn
    have hi (i) : x i ∈ Set.range e := hμ i _ ((Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i))
    apply hx
    refine ⟨fun i => Classical.choose (hi i), ?_⟩
    funext i
    exact Classical.choose_spec (hi i)
  simp only [hp, Complex.ofReal_zero, zero_mul]

theorem movingSamplesPrior_alphabet_sum {A B : Type*} [Fintype A] [Fintype B]
    (e : B ↪ A) (μ : ℕ → A → ℝ) (n : ℕ) (F : MovingSampleSlots A n → ℂ)
    (hμ : ∀ j a, j < n → μ j a ≠ 0 → a ∈ Set.range e) :
    (∑ x : MovingSampleSlots A n, (movingSamplesPrior μ x : ℂ) * F x) =
      ∑ y : MovingSampleSlots B n,
        (movingSamplesPrior (fun j b => μ j (e b)) y : ℂ) * F (y.map e) := by
  rw [movingSamplesPrior_reindex, movingSamplesPrior_reindex]
  rw [productPrior_alphabet_sum e (fun i => μ (movingSampleTier i))
    (fun x => F ((movingSampleCoordinates A n).symm x))
    (fun i a ha => hμ _ a (movingSampleTier_lt i) ha)]
  apply Finset.sum_congr rfl
  intro y _
  congr 2
  apply (movingSampleCoordinates A n).injective
  funext i
  simp only [Equiv.apply_symm_apply, movingSampleCoordinates_map]
  rfl

end Ostmann

end OAI
