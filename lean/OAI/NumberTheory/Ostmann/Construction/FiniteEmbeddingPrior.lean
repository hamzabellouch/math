import OAI.NumberTheory.Ostmann.Construction.FinitePairCells

namespace OAI

/-! # Extending the original finite prior without changing its mean -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def embeddingExtend {A B C : Type*} [Zero C] (e : A ↪ B) (f : A → C) (b : B) : C :=
  if h : ∃ a, e a = b then f h.choose else 0

theorem embeddingExtend_apply {A B C : Type*} [Zero C] (e : A ↪ B) (f : A → C) (a : A) :
    embeddingExtend e f (e a) = f a := by
  have h : ∃ x, e x = e a := ⟨a, rfl⟩
  unfold embeddingExtend
  rw [dite_eq_left h]
  have he : h.choose = a := e.injective h.choose_spec
  rw [he]

theorem embeddingExtend_norm_le {A B : Type*} (e : A ↪ B) (f : A → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ a, ‖f a‖ ≤ C) (b : B) :
    ‖embeddingExtend e f b‖ ≤ C := by
  unfold embeddingExtend
  split_ifs with h
  · exact hf h.choose
  · simpa only [norm_zero] using hC

theorem cellPrior_embedding {A B : Type*} [Fintype A] (e : A ↪ B) (ρ : A → ℝ) (a : A) :
    cellPrior ρ e (e a) = ρ a := by
  unfold cellPrior
  have he (x : A) : e x = e a ↔ x = a := e.injective.eq_iff
  simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem cellPrior_embedding_le {A B : Type*} [Fintype A] (e : A ↪ B) (ρ : A → ℝ)
    (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) (hρ : ∀ a, ρ a ≤ w (e a)) (b : B) :
    cellPrior ρ e b ≤ w b := by
  by_cases h : ∃ a, e a = b
  · obtain ⟨a, rfl⟩ := h
    rw [cellPrior_embedding]
    exact hρ a
  · have he : cellPrior ρ e b = 0 := by
      unfold cellPrior
      apply Finset.sum_eq_zero
      intro a _
      exact ite_eq_right (fun ha => h ⟨a, ha⟩)
    rw [he]
    exact hw b

def intervalSampleEmbedding {A : Type*} (value : A → ℕ) (hinj : Function.Injective value)
    (a N : ℕ) (hlow : ∀ x, a ≤ value x) (hhigh : ∀ x, value x < a + N) : A ↪ Fin N where
  toFun := fun x => ⟨value x - a, by have h₁ := hlow x; have h₂ := hhigh x; omega⟩
  inj' := by
    intro x y hxy
    apply hinj
    have he := congrArg Fin.val hxy
    have hx := hlow x
    have hy := hlow y
    dsimp at he
    omega

theorem intervalSampleEmbedding_value {A : Type*} (value : A → ℕ) (hinj : Function.Injective value)
    (a N : ℕ) (hlow : ∀ x, a ≤ value x) (hhigh : ∀ x, value x < a + N) (x : A) :
    a + (intervalSampleEmbedding value hinj a N hlow hhigh x).val = value x := by
  exact Nat.add_sub_of_le (hlow x)

end Ostmann

end OAI
