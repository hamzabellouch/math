import Mathlib

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
lemma prescribed_permutation_card {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (σ : Equiv.Perm α) :
    (Finset.univ.filter (fun τ : Equiv.Perm α => ∀ x ∈ s, τ x = σ x)).card =
      (Fintype.card α - s.card).factorial := by
  classical
  have hs : Finset.univ.filter (fun τ : Equiv.Perm α => ∀ x ∈ s, τ x = σ x) =
      (permsOfFinset sᶜ).image (fun π => σ * π) := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine ⟨σ⁻¹ * τ, ?_, by simp⟩
      rw [mem_perms_of_finset_iff]
      intro x hx
      simp only [Finset.mem_compl]
      intro hxs
      apply hx
      simp [Equiv.Perm.mul_apply, h x hxs]
    · rintro ⟨π, hπ, rfl⟩ x hx
      have he : π x = x := by
        by_contra he
        have := mem_perms_of_finset_iff.mp hπ he
        simp [hx] at this
      simp [Equiv.Perm.mul_apply, he]
  rw [hs, Finset.card_image_of_injective _ (fun _ _ h => mul_left_cancel h),
    card_perms_of_finset, Finset.card_compl]

lemma prescribed_function_card_le {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (f : α → α) :
    (Finset.univ.filter (fun τ : Equiv.Perm α => ∀ x ∈ s, τ x = f x)).card ≤
      (Fintype.card α - s.card).factorial := by
  classical
  by_cases h : ∃ σ : Equiv.Perm α, ∀ x ∈ s, σ x = f x
  · obtain ⟨σ, hσ⟩ := h
    have he : Finset.univ.filter (fun τ : Equiv.Perm α => ∀ x ∈ s, τ x = f x) =
        Finset.univ.filter (fun τ : Equiv.Perm α => ∀ x ∈ s, τ x = σ x) := by
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> intro h x hx
      · rw [h x hx, hσ x hx]
      · rw [h x hx, hσ x hx]
    rw [he, prescribed_permutation_card]
  · have he : Finset.univ.filter (fun τ : Equiv.Perm α => ∀ x ∈ s, τ x = f x) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro τ _ hτ
      exact h ⟨τ, hτ⟩
    simp [he]

end ThorpCompatibility

end OAI
