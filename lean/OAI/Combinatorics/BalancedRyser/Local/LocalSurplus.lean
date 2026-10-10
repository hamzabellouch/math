import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Local.Local

namespace OAI

namespace Balanced.Local.Surplus

noncomputable section
open scoped BigOperators Classical

theorem exists_retained_subset {α : Type*} [DecidableEq α]
    (U P : Finset α) (c : ℕ) (hPU : P ⊆ U) (hPc : P.card ≤ c) :
    ∃ R : Finset α, P ⊆ R ∧ R ⊆ U ∧ R.card = min c U.card := by
  exact Finset.exists_subsuperset_card_eq hPU
    (le_min hPc (Finset.card_le_card hPU)) (min_le_right _ _)

theorem exists_retained_fibres {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (A : Finset β) (f : α → Option β)
    (P : β → Finset α) (c : β → ℕ)
    (hP : ∀ a ∈ A, P a ⊆ U.filter (fun x => f x = some a))
    (hPc : ∀ a ∈ A, (P a).card ≤ c a) :
    ∃ R : β → Finset α, ∀ a ∈ A,
      P a ⊆ R a ∧ R a ⊆ U.filter (fun x => f x = some a) ∧
      (R a).card = min (c a) (U.filter (fun x => f x = some a)).card := by
  have h : ∀ a, ∃ R : Finset α, a ∈ A →
      P a ⊆ R ∧ R ⊆ U.filter (fun x => f x = some a) ∧
      R.card = min (c a) (U.filter (fun x => f x = some a)).card := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨R, hR⟩ := exists_retained_subset _ _ _ (hP a ha) (hPc a ha)
      exact ⟨R, fun _ => hR⟩
    · exact ⟨∅, fun h => False.elim (ha h)⟩
  choose R hR using h
  exact ⟨R, hR⟩

theorem precovered_mem_surplus {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (A : Finset β) (f : α → Option β)
    (R : β → Finset α)
    (hR : ∀ a ∈ A, R a ⊆ U.filter (fun x => f x = some a))
    {x : α} (hx : x ∈ U) (hf : f x = none) :
    x ∈ U \ A.biUnion R := by
  apply Finset.mem_sdiff.mpr
  refine ⟨hx, ?_⟩
  intro hm
  obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hm
  have hsome := (Finset.mem_filter.mp (hR a ha hxa)).2
  simp [hf] at hsome

theorem surplus_not_protected {α β : Type*} [DecidableEq α]
    (U : Finset α) (A : Finset β) (P R : β → Finset α)
    (hP : ∀ a ∈ A, P a ⊆ R a) {a : β} (ha : a ∈ A)
    {x : α} (hx : x ∈ U \ A.biUnion R) : x ∉ P a := by
  intro hp
  exact (Finset.mem_sdiff.mp hx).2
    (Finset.mem_biUnion.mpr ⟨a, ha, hP a ha hp⟩)

theorem card_surplus_ge {α β : Type*} [DecidableEq α]
    (U : Finset α) (A : Finset β) (R : β → Finset α) (c : β → ℕ)
    (hR : ∀ a ∈ A, (R a).card ≤ c a) :
    U.card - ∑ a ∈ A, c a ≤ (U \ A.biUnion R).card := by
  have hret : (A.biUnion R).card ≤ ∑ a ∈ A, c a :=
    (Finset.card_biUnion_le).trans (Finset.sum_le_sum hR)
  have hdiff := Finset.card_sdiff_add_card_inter U (A.biUnion R)
  have hinter := Finset.card_le_card (Finset.inter_subset_right :
    U ∩ A.biUnion R ⊆ A.biUnion R)
  omega

theorem source_surplus_card_ge {α β : Type*} [DecidableEq α]
    (U : Finset α) (A : Finset β) (R : β → Finset α) (c : β → ℕ)
    (b κ : ℕ) (hb : 1 ≤ b) (hU : U.card = 4 * b)
    (hA : A.card ≤ b - 1) (hR : ∀ a ∈ A, (R a).card ≤ c a)
    (hcap : (∑ a ∈ A, c a) ≤ 2 * A.card + 2 * κ) :
    2 * b + 2 - 2 * κ ≤ (U \ A.biUnion R).card := by
  have h := card_surplus_ge U A R c hR
  omega

theorem source_independent_surplus_card_ge {α β : Type*} [DecidableEq α]
    (U : Finset α) (A : Finset β) (R : β → Finset α) (c : β → ℕ)
    (D : Finset α) (b κ : ℕ) (hb : 1 ≤ b) (hU : U.card = 4 * b)
    (hA : A.card ≤ b - 1) (hR : ∀ a ∈ A, (R a).card ≤ c a)
    (hcap : (∑ a ∈ A, c a) ≤ 2 * A.card + 2 * κ)
    (hD : D.card ≤ 2 * κ) :
    2 * b + 2 - 4 * κ ≤ ((U \ A.biUnion R) \ D).card := by
  have h := source_surplus_card_ge U A R c b κ hb hU hA hR hcap
  have hdiff := Finset.card_sdiff_add_card_inter (U \ A.biUnion R) D
  have hinter := Finset.card_le_card (Finset.inter_subset_right :
    (U \ A.biUnion R) ∩ D ⊆ D)
  omega

end
end Balanced.Local.Surplus

end OAI
