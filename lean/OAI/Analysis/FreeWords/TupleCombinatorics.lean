import Mathlib

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

def tupleLabels {n : ℕ} (a : Fin n → α) : Multiset α := List.ofFn a

def tupleFiber (n : ℕ) (W : Multiset α) : Finset (Fin n → α) :=
  Finset.univ.filter (fun a => tupleLabels a = W)

theorem tupleFiber_card (n : ℕ) (W : Multiset α) :
    (tupleFiber n W).card ≤ n.factorial := by
  classical
  by_cases h : (tupleFiber n W).Nonempty
  · obtain ⟨a, ha⟩ := h
    have haW : tupleLabels a = W := (Finset.mem_filter.mp ha).2
    calc
      _ = ((tupleFiber n W).image List.ofFn).card :=
        (Finset.card_image_of_injective _ List.ofFn_injective).symm
      _ ≤ ((List.ofFn a).permutations.toFinset).card := by
        apply Finset.card_le_card
        intro l hl
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hl
        apply List.mem_toFinset.mpr
        apply List.mem_permutations.mpr
        apply Multiset.coe_eq_coe.mp
        exact ((Finset.mem_filter.mp hb).2).trans haW.symm
      _ ≤ (List.ofFn a).permutations.length := List.toFinset_card_le _
      _ = n.factorial := by rw [List.length_permutations, List.length_ofFn]
  · rw [Finset.not_nonempty_iff_eq_empty.mp h]
    simp

theorem tuple_completion_card (n : ℕ) (U W : Multiset α) :
    (Finset.univ.filter (fun a : Fin n → α => U + tupleLabels a = W)).card ≤
      n.factorial := by
  classical
  let s := Finset.univ.filter (fun a : Fin n → α => U + tupleLabels a = W)
  by_cases hs : s.Nonempty
  · obtain ⟨a, ha⟩ := hs
    have he : s = tupleFiber n (tupleLabels a) := by
      ext b
      simp only [s, tupleFiber, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← (Finset.mem_filter.mp ha).2, add_left_cancel_iff]
    change s.card ≤ _
    rw [he]
    exact tupleFiber_card n (tupleLabels a)
  · exact (Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hs)).le.trans
      (Nat.zero_le _)

omit [Fintype α] [DecidableEq α] in
@[simp] theorem tupleLabels_cons {n : ℕ} (c : α) (a : Fin n → α) :
    tupleLabels (Fin.cons c a) = {c} + tupleLabels a := by
  simp [tupleLabels, Multiset.singleton_add]

theorem sum_card_tuple_completion (n : ℕ) (U W : Multiset α) :
    (∑ a : Fin n → α,
      (Finset.univ.filter (fun c : α => U + {c} + tupleLabels a = W)).card) ≤
      (n + 1).factorial := by
  have he : (∑ a : Fin n → α,
      (Finset.univ.filter (fun c : α => U + {c} + tupleLabels a = W)).card) =
      (Finset.univ.filter (fun a : Fin (n+1) → α => U + tupleLabels a = W)).card := by
    simp only [Finset.card_filter]
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => α))
      (fun a => if U + tupleLabels a = W then (1 : ℕ) else 0)]
    rw [Fintype.sum_prod_type]
    have hc (c : α) (a : Fin n → α) :
        tupleLabels ((Fin.consEquiv (fun _ : Fin (n+1) => α)) (c,a)) =
          {c} + tupleLabels a := tupleLabels_cons c a
    simp only [hc, ← add_assoc]
    exact Finset.sum_comm
  rw [he]
  exact tuple_completion_card (n+1) U W

end

end KKFreeWords
end

end OAI
