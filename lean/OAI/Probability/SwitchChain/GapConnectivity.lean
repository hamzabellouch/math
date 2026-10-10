import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FiniteMarkov

variable {α : Type*} [Fintype α]

theorem harmonic_constant
    (P : α → α → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hgap : ∀ f : α → ℝ,
      γ * (∑ x, (f x - (∑ y, f y) / (Fintype.card α : ℝ)) ^ 2) ≤
        ∑ x, f x * (f x - ∑ y, P x y * f y))
    (f : α → ℝ) (hf : ∀ x, ∑ y, P x y * f y = f x) :
    ∀ x y, f x = f y := by
  have henergy : (∑ x, f x * (f x - ∑ y, P x y * f y)) = 0 := by
    simp [hf]
  have hsum_nonneg : 0 ≤ ∑ x, (f x - (∑ y, f y) / (Fintype.card α : ℝ)) ^ 2 := by
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum : (∑ x, (f x - (∑ y, f y) / (Fintype.card α : ℝ)) ^ 2) = 0 := by
    have h := hgap f
    rw [henergy] at h
    nlinarith
  have hpoint : ∀ x, f x = (∑ y, f y) / (Fintype.card α : ℝ) := by
    intro x
    have hx : (f x - (∑ y, f y) / (Fintype.card α : ℝ)) ^ 2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hsum x (Finset.mem_univ x)
    nlinarith [sq_nonneg (f x - (∑ y, f y) / (Fintype.card α : ℝ))]
  intro x y
  exact (hpoint x).trans (hpoint y).symm

theorem reachable_of_poincare
    (P : α → α → ℝ) (r : α → α → Prop)
    (hr : ∀ ⦃a b⦄, r a b → r b a)
    (hsupport : ∀ x y, P x y ≠ 0 → x = y ∨ r x y)
    (hrows : ∀ x, ∑ y, P x y = 1)
    (γ : ℝ) (hγ : 0 < γ)
    (hgap : ∀ f : α → ℝ,
      γ * (∑ x, (f x - (∑ y, f y) / (Fintype.card α : ℝ)) ^ 2) ≤
        ∑ x, f x * (f x - ∑ y, P x y * f y)) :
    ∀ x y, Relation.ReflTransGen r x y := by
  classical
  intro x y
  let f : α → ℝ := fun z => if Relation.ReflTransGen r x z then 1 else 0
  have hsame : ∀ a b, P a b ≠ 0 → f a = f b := by
    intro a b hab
    rcases hsupport a b hab with heq | hedge
    · rw [heq]
    · have hab' : Relation.ReflTransGen r a b := Relation.ReflTransGen.single hedge
      have hba' : Relation.ReflTransGen r b a := Relation.ReflTransGen.single (hr hedge)
      have hiff : Relation.ReflTransGen r x a ↔ Relation.ReflTransGen r x b :=
        ⟨fun h => h.trans hab', fun h => h.trans hba'⟩
      simp only [f, hiff]
  have hf : ∀ a, ∑ b, P a b * f b = f a := by
    intro a
    calc
      (∑ b, P a b * f b) = ∑ b, P a b * f a := by
        apply Finset.sum_congr rfl
        intro b _
        by_cases h : P a b = 0
        · simp [h]
        · rw [hsame a b h]
      _ = (∑ b, P a b) * f a := (Finset.sum_mul _ _ _).symm
      _ = f a := by rw [hrows, one_mul]
  have heq := harmonic_constant P γ hγ hgap f hf x y
  have hx : f x = 1 := by simp [f, Relation.ReflTransGen.refl]
  by_contra hy
  have hy' : f y = 0 := by simp [f, hy]
  rw [hx, hy'] at heq
  norm_num at heq

end Problem315.FiniteMarkov

end

end OAI
