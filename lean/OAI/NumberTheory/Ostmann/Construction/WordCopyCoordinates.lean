import Mathlib.Logic.Equiv.Fin.Basic
import OAI.NumberTheory.Ostmann.Construction.DoubledWordExpansion
import OAI.NumberTheory.Ostmann.Construction.RepeatedTuplePoisson

namespace OAI

/-! # The two copies of every word and cell role as one ordered tuple -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def wordCopyEquiv (A : Type*) (k m : ℕ) :
    (((Fin k → A) × (Fin m → A)) × ((Fin k → A) × (Fin m → A))) ≃
      (Fin ((k + m) + (k + m)) → A) :=
  ((Fin.appendEquiv k m).prodCongr (Fin.appendEquiv k m)).trans
    (Fin.appendEquiv (k + m) (k + m))

theorem map_fin_append {A B : Type*} {k m : ℕ} (f : A → B)
    (x : Fin k → A) (y : Fin m → A) :
    Fin.append (f ∘ x) (f ∘ y) = f ∘ Fin.append x y := by
  funext i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin k ⊕ Fin m ≃ Fin (k + m)).surjective i
  cases j with
  | inl j => simp only [finSumFinEquiv_apply_left, Fin.append_left, Function.comp_apply]
  | inr j => simp only [finSumFinEquiv_apply_right, Fin.append_right, Function.comp_apply]

theorem wordCopyEquiv_map {A B : Type*} {k m : ℕ} (f : A → B)
    (z : ((Fin k → A) × (Fin m → A)) × ((Fin k → A) × (Fin m → A))) :
    wordCopyEquiv B k m ((f ∘ z.1.1, f ∘ z.1.2), (f ∘ z.2.1, f ∘ z.2.2)) =
      f ∘ wordCopyEquiv A k m z := by
  change Fin.append (Fin.append (f ∘ z.1.1) (f ∘ z.1.2))
    (Fin.append (f ∘ z.2.1) (f ∘ z.2.2)) = f ∘ Fin.append (Fin.append z.1.1 z.1.2) (Fin.append z.2.1 z.2.2)
  rw [map_fin_append, map_fin_append, map_fin_append]

theorem productPrior_append {A : Type*} {k m : ℕ}
    (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ) (x : Fin k → A) (y : Fin m → A) :
    productPrior (Fin.append μ ν) (Fin.append x y) = productPrior μ x * productPrior ν y := by
  simp only [productPrior, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

theorem wordCopyPrior {A : Type*} {k m : ℕ}
    (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ)
    (z : ((Fin k → A) × (Fin m → A)) × ((Fin k → A) × (Fin m → A))) :
    productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) (wordCopyEquiv A k m z) =
      jointWordPrior μ ν z.1 * jointWordPrior μ ν z.2 := by
  change productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν))
    (Fin.append (Fin.append z.1.1 z.1.2) (Fin.append z.2.1 z.2.2)) = _
  rw [productPrior_append, productPrior_append, productPrior_append]
  rfl

noncomputable def wordCopyCharacter (k m : ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) :
    Fin ((k + m) + (k + m)) → ∀ p : ℕ, DirichletCharacter ℂ p :=
  Fin.append (fun _ p => χ p) (fun _ p => (χ p)⁻¹)

theorem wordCopyCharacter_product {k m : ℕ}
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p) (a : ℤ)
    (z : ((Fin k → ℕ) × (Fin m → ℕ)) × ((Fin k → ℕ) × (Fin m → ℕ))) :
    (∏ i, wordCopyCharacter k m χ i (wordCopyEquiv ℕ k m z i)
      ((a : ZMod (wordCopyEquiv ℕ k m z i)) - t (wordCopyEquiv ℕ k m z i))) =
      ((∏ i, χ (z.1.1 i) ((a : ZMod (z.1.1 i)) - t (z.1.1 i))) *
        (∏ i, χ (z.1.2 i) ((a : ZMod (z.1.2 i)) - t (z.1.2 i)))) *
      conj ((∏ i, χ (z.2.1 i) ((a : ZMod (z.2.1 i)) - t (z.2.1 i))) *
        (∏ i, χ (z.2.2 i) ((a : ZMod (z.2.2 i)) - t (z.2.2 i)))) := by
  let f (p : ℕ) := χ p ((a : ZMod p) - t p)
  let u := wordCopyEquiv ℕ k m z
  have he : (∏ i, wordCopyCharacter k m χ i (u i) ((a : ZMod (u i)) - t (u i))) =
      ∏ i, Fin.append (fun _ : Fin (k + m) => f) (fun _ : Fin (k + m) => conj ∘ f) i (u i) := by
    apply Finset.prod_congr rfl
    intro i _
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [wordCopyCharacter, Fin.append_left]
      rfl
    · simp only [wordCopyCharacter, Fin.append_right]
      exact (MulChar.star_apply' (χ _) _).symm
  rw [he]
  change (∏ i, Fin.append (fun _ : Fin (k + m) => f) (fun _ : Fin (k + m) => conj ∘ f) i
    (Fin.append (Fin.append z.1.1 z.1.2) (Fin.append z.2.1 z.2.2) i)) = _
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [Fin.prod_univ_add, Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right, Function.comp_apply, map_mul, map_prod]
  rfl

theorem wordCopyAmplitude {B : Type*} {k m : ℕ}
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p) (a : ℤ)
    (bin : (Fin k → ℕ) → B) (b : B)
    (z : ((Fin k → ℕ) × (Fin m → ℕ)) × ((Fin k → ℕ) × (Fin m → ℕ))) :
    jointWordAmplitude (fun _ p => χ p ((a : ZMod p) - t p))
        (fun _ p => χ p ((a : ZMod p) - t p)) bin b z.1 *
      conj (jointWordAmplitude (fun _ p => χ p ((a : ZMod p) - t p))
        (fun _ p => χ p ((a : ZMod p) - t p)) bin b z.2) =
      if bin z.1.1 = b ∧ bin z.2.1 = b then
        ∏ i, wordCopyCharacter k m χ i (wordCopyEquiv ℕ k m z i)
          ((a : ZMod (wordCopyEquiv ℕ k m z i)) - t (wordCopyEquiv ℕ k m z i))
      else 0 := by
  by_cases h₁ : bin z.1.1 = b <;> by_cases h₂ : bin z.2.1 = b
  · simp only [jointWordAmplitude, h₁, h₂, ite_true, and_self]
    exact (wordCopyCharacter_product χ t a z).symm
  · simp [jointWordAmplitude, h₁, h₂]
  · simp [jointWordAmplitude, h₁, h₂]
  · simp [jointWordAmplitude, h₁, h₂]

theorem wordCopyAmplitude_map {A B : Type*} {k m : ℕ} (v : A → ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p) (a : ℤ)
    (bin : (Fin k → A) → B) (b : B)
    (z : ((Fin k → A) × (Fin m → A)) × ((Fin k → A) × (Fin m → A))) :
    jointWordAmplitude (fun _ p => χ (v p) ((a : ZMod (v p)) - t (v p)))
        (fun _ p => χ (v p) ((a : ZMod (v p)) - t (v p))) bin b z.1 *
      conj (jointWordAmplitude (fun _ p => χ (v p) ((a : ZMod (v p)) - t (v p)))
        (fun _ p => χ (v p) ((a : ZMod (v p)) - t (v p))) bin b z.2) =
      if bin z.1.1 = b ∧ bin z.2.1 = b then
        ∏ i, wordCopyCharacter k m χ i (v (wordCopyEquiv A k m z i))
          ((a : ZMod (v (wordCopyEquiv A k m z i))) - t (v (wordCopyEquiv A k m z i)))
      else 0 := by
  by_cases h₁ : bin z.1.1 = b <;> by_cases h₂ : bin z.2.1 = b
  · simp only [jointWordAmplitude, h₁, h₂, ite_true, and_self]
    have hh := wordCopyCharacter_product χ t a
      ((v ∘ z.1.1, v ∘ z.1.2), (v ∘ z.2.1, v ∘ z.2.2))
    rw [wordCopyEquiv_map] at hh
    simpa only [Function.comp_apply] using hh.symm
  · simp [jointWordAmplitude, h₁, h₂]
  · simp [jointWordAmplitude, h₁, h₂]
  · simp [jointWordAmplitude, h₁, h₂]

theorem wordCopyCharacter_ne_one {k m : ℕ}
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (p : ℕ) (hχ : χ p ≠ 1)
    (i : Fin ((k + m) + (k + m))) : wordCopyCharacter k m χ i p ≠ 1 := by
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin (k + m) ⊕ Fin (k + m) ≃
    Fin ((k + m) + (k + m))).surjective i
  cases j with
  | inl j => simpa only [finSumFinEquiv_apply_left, wordCopyCharacter, Fin.append_left] using hχ
  | inr j => simpa only [finSumFinEquiv_apply_right, wordCopyCharacter, Fin.append_right,
      ne_eq, inv_eq_one] using hχ

end Ostmann

end OAI
