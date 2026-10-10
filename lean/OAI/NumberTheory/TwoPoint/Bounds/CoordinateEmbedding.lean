import OAI.NumberTheory.TwoPoint.Walks.SelectedPairRank
import OAI.NumberTheory.TwoPoint.Bounds.FormalDepartures
import Mathlib.LinearAlgebra.Pi

namespace OAI

/-! Removing unused prime labels preserves the selected-pair rank. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

variable {α β ρ : Type*} [Fintype α] [Fintype β]

lemma extendByZero_basis (e : α → β) (he : Function.Injective e) (a : α) :
    Function.ExtendByZero.linearMap ℝ e (Pi.basisFun ℝ α a) = Pi.basisFun ℝ β (e a) := by
  classical
  ext b
  by_cases hb : ∃ c, e c = b
  · obtain ⟨c, rfl⟩ := hb
    change Function.extend e (Pi.basisFun ℝ α a) 0 (e c) = _
    rw [he.extend_apply]
    simp [Pi.basisFun_apply, Pi.single_apply, he.eq_iff]
  · change Function.extend e (Pi.basisFun ℝ α a) 0 b = _
    rw [Function.extend_apply' _ _ _ hb]
    have hne : b ≠ e a := fun h => hb ⟨a, h.symm⟩
    simp [Pi.basisFun_apply, hne]

omit [Fintype α] [Fintype β] in
lemma extendByZero_injective (e : α → β) (he : Function.Injective e) :
    Function.Injective (Function.ExtendByZero.linearMap ℝ e) := by
  intro x y hxy
  funext a
  have h := congrFun hxy (e a)
  simpa only [Function.ExtendByZero.linearMap_apply, he.extend_apply] using h

lemma formalDeparture_extend (e : α → β) (he : Function.Injective e)
    (label : ℕ → α) (coefficient : ℕ → ℝ) (n : ℕ) :
    Function.ExtendByZero.linearMap ℝ e (formalDeparture label coefficient n) =
      formalDeparture (e ∘ label) coefficient n := by
  unfold formalDeparture
  simp only [map_sum, map_smul, extendByZero_basis e he, Function.comp_apply]

/-- In particular, a rank witness in the ambient prime pool is equivalent
to the witness on its observed equality classes. -/
theorem selected_rank_rename_iff (e : α → β) (he : Function.Injective e)
    (label : ℕ → α) (coefficient : ℕ → ℝ) (left right : ρ → ℕ) (control : ρ → α) :
    LinearIndependent ℝ (Sum.elim
      (fun i => formalDeparture label coefficient (left i) - formalDeparture label coefficient (right i))
      (fun i => Pi.basisFun ℝ α (control i))) ↔
    LinearIndependent ℝ (Sum.elim
      (fun i => formalDeparture (e ∘ label) coefficient (left i) -
        formalDeparture (e ∘ label) coefficient (right i))
      (fun i => Pi.basisFun ℝ β (e (control i)))) := by
  let E := Function.ExtendByZero.linearMap ℝ e
  have hfamily : (E ∘ Sum.elim
      (fun i => formalDeparture label coefficient (left i) - formalDeparture label coefficient (right i))
      (fun i => Pi.basisFun ℝ α (control i))) = Sum.elim
      (fun i => formalDeparture (e ∘ label) coefficient (left i) -
        formalDeparture (e ∘ label) coefficient (right i))
      (fun i => Pi.basisFun ℝ β (e (control i))) := by
    funext i
    rcases i with i | i
    · exact (map_sub E _ _).trans (congrArg₂ (· - ·)
        (formalDeparture_extend e he label coefficient (left i))
        (formalDeparture_extend e he label coefficient (right i)))
    · exact extendByZero_basis e he (control i)
  constructor
  · intro h
    rw [← hfamily]
    exact h.map' E (LinearMap.ker_eq_bot.mpr (extendByZero_injective e he))
  · intro h
    rw [← hfamily] at h
    exact LinearIndependent.of_comp E h

end TwoPointCorrelations

end OAI
