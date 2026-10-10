import OAI.NumberTheory.TwoPoint.Halasz.HalaszFiniteHolder
import OAI.NumberTheory.TwoPoint.Halasz.HalaszFiberEnergy

namespace OAI

/-! Weighted Hölder after grouping tuples by their complete-system
frequency. The square multiplicity sum is exactly the Vinogradov energy. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_fiber_norm_sum {α β : Type*} (F : Finset α) (f : α → β) (z : β → ℂ) :
    ‖∑ a∈F,z (f a)‖≤∑ c∈F.image f,((F.filter (fun a => f a=c)).card:ℝ)*‖z c‖ := by
  apply (norm_sum_le _ _).trans_eq
  rw [← sum_fiberwise_of_maps_to (s := F) (t := F.image f) (g := f)
    (fun a ha => mem_image_of_mem f ha)]
  apply sum_congr rfl
  intro c _
  calc
    _ = ∑ _a∈F.filter (fun a => f a=c), ‖z c‖ := by
      apply sum_congr rfl
      intro a ha
      rw [(mem_filter.mp ha).2]
    _ = _ := by simp

theorem halasz_fiber_holder {α β : Type*} (F : Finset α) (f : α → β)
    (z : β → ℂ) {s : ℕ} (hs : 1≤s) :
    ‖∑ a∈F,z (f a)‖^(2*s) ≤ (F.card:ℝ)^(2*s-2)*
      (halaszFiberEnergy F f:ℝ)*(∑ c∈F.image f,‖z c‖^(2*s)) := by
  have h := halasz_finite_weighted_holder (F.image f)
    (fun c => ((F.filter (fun a => f a=c)).card:ℝ)) (fun c => ‖z c‖)
    (fun _ => Nat.cast_nonneg _) (fun _ => norm_nonneg _) hs
  have hcard : (∑ c∈F.image f,((F.filter (fun a => f a=c)).card:ℝ))=(F.card:ℝ) := by
    exact_mod_cast (card_eq_sum_card_image f F).symm
  have henergy : (∑ c∈F.image f,((F.filter (fun a => f a=c)).card:ℝ)^2)=
      (halaszFiberEnergy F f:ℝ) := by
    simp only [halaszFiberEnergy,Nat.cast_sum,Nat.cast_pow]
  rw [hcard,henergy] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) (halasz_fiber_norm_sum F f z) _).trans h

end TwoPointCorrelations

end OAI
