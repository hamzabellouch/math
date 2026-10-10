import Mathlib.Data.Finset.Option
import OAI.NumberTheory.Ostmann.Characters.PrimitiveCharacterReduction

namespace OAI

/-! # Transport of coefficients along an injective character reduction -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def injectiveCoefficient {α β : Type*} (f : α → β) (w : α → ℂ)
    (b : β) : ℂ := if h : ∃ a, f a = b then w h.choose else 0

theorem injectiveCoefficient_apply {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (w : α → ℂ) (a : α) : injectiveCoefficient f w (f a) = w a := by
  unfold injectiveCoefficient
  rw [dite_eq_left ⟨a, rfl⟩]
  congr 1
  exact hf (Exists.choose_spec (show ∃ a', f a' = f a from ⟨a, rfl⟩))

theorem injectiveCoefficient_norm_le {α β : Type*} (f : α → β) (w : α → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hw : ∀ a, ‖w a‖ ≤ B) (b : β) :
    ‖injectiveCoefficient f w b‖ ≤ B := by
  unfold injectiveCoefficient
  split_ifs with h
  · exact hw h.choose
  · simpa only [norm_zero] using hB

theorem injectiveCoefficient_ne_zero {α β : Type*} (f : α → β) (w : α → ℂ)
    (b : β) (hb : injectiveCoefficient f w b ≠ 0) :
    ∃ a, f a = b ∧ w a ≠ 0 := by
  unfold injectiveCoefficient at hb
  split_ifs at hb with h
  · exact ⟨h.choose, h.choose_spec, hb⟩
  · exact (hb rfl).elim

theorem injectiveCoefficient_sum {α β : Type*} [Fintype α]
    (f : α → β) (hf : Function.Injective f) (w : α → ℂ) (g : β → ℂ) :
    (∑ b ∈ ((Finset.univ : Finset α).filter (fun a => w a ≠ 0)).image f,
      injectiveCoefficient f w b * g b) = ∑ a, w a * g (f a) := by
  rw [Finset.sum_image (fun a _ b _ h => hf h)]
  simp_rw [injectiveCoefficient_apply f hf w]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : w a = 0 <;> simp [h]

/-- Splitting a finite option family isolates the unique principal coefficient. -/
theorem sum_option_support {β : Type*} (S : Finset (Option β)) (h : Option β → ℂ)
    (hzero : none ∉ S → h none = 0) :
    (∑ e ∈ S, h e) = h none + ∑ b ∈ S.eraseNone, h (some b) := by
  have hs : (∑ b ∈ S.eraseNone, h (some b)) = ∑ e ∈ S.erase none, h e := by
    rw [← Finset.image_some_eraseNone S, Finset.sum_image
      (fun a _ b _ hab => Option.some.inj hab)]
  rw [hs]
  by_cases hn : none ∈ S
  · exact (Finset.add_sum_erase S h hn).symm
  · rw [Finset.erase_eq_of_notMem hn, hzero hn, zero_add]

end Ostmann

end OAI
