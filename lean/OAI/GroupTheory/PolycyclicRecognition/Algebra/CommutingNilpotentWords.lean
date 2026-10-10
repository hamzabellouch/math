import OAI.GroupTheory.PolycyclicRecognition.Algebra.ActionWordFiltration
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.RingTheory.Nilpotent.Basic
import Lean.Elab.Tactic.Omega

namespace OAI

/-! # Uniform vanishing of words in finitely many commuting nilpotents -/

noncomputable section
namespace PolycyclicRecognition
variable {R : Type*} [Ring R]

theorem commuting_nilpotent_words_zero (ss : List R)
    (hpair : ∀ a ∈ ss, ∀ b ∈ ss, Commute a b) (hnil : ∀ a ∈ ss, IsNilpotent a) :
    ∃ c : ℕ, ∀ w : List R, (∀ a ∈ w, a ∈ ss) → c ≤ w.length → w.prod = 0 := by
  classical
  induction ss with
  | nil =>
    refine ⟨1, ?_⟩
    intro w hw hlen
    cases w with
    | nil => simp at hlen
    | cons x xs => exact False.elim (List.not_mem_nil (hw x (by simp)))
  | cons a ss ih =>
    obtain ⟨n, hn⟩ := hnil a (by simp)
    obtain ⟨m, hm⟩ := ih
      (fun x hx y hy => hpair x (by simp [hx]) y (by simp [hy]))
      (fun x hx => hnil x (by simp [hx]))
    refine ⟨n + m, ?_⟩
    intro w hw hlen
    let w₀ := w.filter (fun x => decide (x = a))
    let w₁ := w.filter (fun x => decide (x ≠ a))
    have hp : w.Perm (w₀ ++ w₁) := by
      simpa [w₀, w₁] using (List.filter_append_perm (fun x => decide (x = a)) w).symm
    have hc : w.Pairwise Commute := List.pairwise_of_forall_mem_list
      (fun x hx y hy => hpair x (hw x hx) y (hw y hy))
    have hprod := hp.prod_eq' hc
    rw [List.prod_append] at hprod
    have hw₀ : w₀.prod = a ^ w₀.length := List.prod_eq_pow_length _ _ (by
      intro x hx
      exact of_decide_eq_true (List.mem_filter.mp hx).2)
    rw [hw₀] at hprod
    rw [hprod]
    by_cases hlarge : n ≤ w₀.length
    · have hzero : a ^ w₀.length = 0 := by
        have he : w₀.length = n + (w₀.length - n) := by omega
        rw [he, pow_add, hn, zero_mul]
      rw [hzero, zero_mul]
    · have hlength := hp.length_eq
      rw [List.length_append] at hlength
      have hmle : m ≤ w₁.length := by omega
      have hw₁ : ∀ x ∈ w₁, x ∈ ss := by
        intro x hx
        obtain ⟨hxw, hxa⟩ := List.mem_filter.mp hx
        have hne : x ≠ a := of_decide_eq_true hxa
        exact (List.mem_cons.mp (hw x hxw)).resolve_left hne
      rw [hm w₁ hw₁ hmle, mul_zero]

theorem finite_commuting_nilpotent_action_filtration
    {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I]
    (D : I → Module.End K V) (hcomm : ∀ i j, Commute (D i) (D j))
    (hnil : ∀ i, IsNilpotent (D i)) :
    ∃ c, linearActionFiltration D c = ⊥ := by
  classical
  let ss := (Finset.univ.toList.map D)
  have hss : ∀ x ∈ ss, ∃ i, x = D i := by
    intro x hx
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hx
    exact ⟨i, hi.symm⟩
  obtain ⟨c, hc⟩ := commuting_nilpotent_words_zero ss
    (by intro x hx y hy; obtain ⟨i, rfl⟩ := hss x hx; obtain ⟨j, rfl⟩ := hss y hy; exact hcomm i j)
    (by intro x hx; obtain ⟨i, rfl⟩ := hss x hx; exact hnil i)
  refine ⟨c, linearActionFiltration_eq_bot_of_word_zero D c ?_⟩
  intro w hw
  apply hc (w.map D)
  · intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact List.mem_map.mpr ⟨i, by simp, rfl⟩
  · simpa only [List.length_map, hw] using (le_refl c)

end PolycyclicRecognition

end

end OAI
