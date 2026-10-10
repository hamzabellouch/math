import Mathlib

namespace OAI

namespace Problem340
namespace MonotoneItineraries

open Finset

def labelSum {N H : ℕ} (v : Fin N → Fin H) : ℕ :=
  ∑ i, (v i).val

lemma labelSum_le {N H : ℕ} (v : Fin N → Fin H) :
    labelSum v ≤ N * (H - 1) := by
  calc
    labelSum v ≤ ∑ _i : Fin N, (H - 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.le_sub_one_of_lt (v i).is_lt
    _ = N * (H - 1) := by simp

lemma eq_of_le_of_labelSum_eq {N H : ℕ} {v w : Fin N → Fin H}
    (hvw : v ≤ w) (hsum : labelSum v = labelSum w) : v = w := by
  funext i
  apply Fin.ext
  exact (Finset.sum_eq_sum_iff_of_le (fun j _ => show (v j).val ≤ (w j).val from hvw j)).mp hsum i (Finset.mem_univ i)

theorem card_range_le {α : Type*} [LinearOrder α] {N H : ℕ}
    (c : α → Fin N → Fin H) (hc : Monotone c) :
    Nat.card (Set.range c) ≤ 1 + N * (H - 1) := by
  classical
  let := Fintype.ofFinite (Set.range c)
  let rank : Set.range c → Fin (N * (H - 1) + 1) :=
    fun v => ⟨labelSum v.val, Nat.lt_succ_of_le (labelSum_le v.val)⟩
  have hrank : Function.Injective rank := by
    intro v w heq
    apply Subtype.ext
    have hsum : labelSum v.val = labelSum w.val := congrArg Fin.val heq
    obtain ⟨x, hx⟩ := v.property
    obtain ⟨y, hy⟩ := w.property
    rcases le_total x y with hxy | hyx
    · exact eq_of_le_of_labelSum_eq (hx ▸ hy ▸ hc hxy) hsum
    · exact (eq_of_le_of_labelSum_eq (hy ▸ hx ▸ hc hyx) hsum.symm).symm
  simpa [Nat.card_eq_fintype_card, Nat.add_comm] using
    Fintype.card_le_of_injective rank hrank

def itinerary {α : Type*} {H : ℕ} (R : α → α) (b : α → Fin H)
    (N : ℕ) (x : α) : Fin N → Fin H := fun i => b (R^[i.val] x)

lemma itinerary_monotone {α : Type*} [Preorder α] {H : ℕ}
    {R : α → α} {b : α → Fin H} (hR : Monotone R) (hb : Monotone b) (N : ℕ) :
    Monotone (itinerary R b N) := by
  intro x y hxy i
  exact hb ((hR.iterate i.val) hxy)

theorem card_itinerary_range_le {α : Type*} [LinearOrder α] {H : ℕ}
    {R : α → α} {b : α → Fin H} (hR : Monotone R) (hb : Monotone b) (N : ℕ) :
    Nat.card (Set.range (itinerary R b N)) ≤ 1 + N * (H - 1) :=
  card_range_le _ (itinerary_monotone hR hb N)

end MonotoneItineraries
end Problem340

end OAI
