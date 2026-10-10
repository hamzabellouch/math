import Mathlib

namespace OAI

noncomputable section
open scoped Classical

namespace Problem315.BinaryAssignments

variable {α : Type*} [Fintype α]

def singletons (c : α → Nat) : Finset α := Finset.univ.filter (fun w => c w = 1)
def common (c : α → Nat) : Finset α := Finset.univ.filter (fun w => c w = 2)

def first (c : α → Nat) (U : Finset α) (w : α) : Prop := c w = 2 ∨ w ∈ U
def second (c : α → Nat) (U : Finset α) (w : α) : Prop :=
  c w = 2 ∨ (c w = 1 ∧ w ∉ U)

theorem indicator_sum (c : α → Nat) (hc : ∀ w, c w ≤ 2)
    (U : Finset α) (hU : U ⊆ singletons c) (w : α) :
    (if first c U w then 1 else 0) + (if second c U w then 1 else 0) = c w := by
  have hw := hc w
  have hmem : w ∈ U → c w = 1 := fun h => (Finset.mem_filter.mp (hU h)).2
  by_cases hu : w ∈ U
  · have hc1 := hmem hu
    simp [first, second, hu, hc1]
  · rcases (show c w = 0 ∨ c w = 1 ∨ c w = 2 by omega) with h | h | h <;>
      simp [first, second, hu, h]

theorem first_on_singletons (c : α → Nat) (U : Finset α) (w : α)
    (hw : w ∈ singletons c) : first c U w ↔ w ∈ U := by
  have hc := (Finset.mem_filter.mp hw).2
  simp [first, hc]

theorem first_filter (c : α → Nat) (U : Finset α) :
    Finset.univ.filter (first c U) = common c ∪ U := by
  ext w
  simp [first, common]

theorem second_filter (c : α → Nat) (U : Finset α) :
    Finset.univ.filter (second c U) = common c ∪ (singletons c \ U) := by
  ext w
  simp [second, common, singletons]

theorem first_card (c : α → Nat) (U : Finset α) (hU : U ⊆ singletons c) :
    (Finset.univ.filter (first c U)).card = (common c).card + U.card := by
  rw [first_filter, Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro w hw hwu
  have h2 := (Finset.mem_filter.mp hw).2
  have h1 := (Finset.mem_filter.mp (hU hwu)).2
  omega

theorem second_card_add (c : α → Nat) (U : Finset α) (hU : U ⊆ singletons c) :
    (Finset.univ.filter (second c U)).card + U.card =
      (common c).card + (singletons c).card := by
  have hdis : Disjoint (common c) (singletons c \ U) := by
    apply Finset.disjoint_left.mpr
    intro w hw hws
    have h2 := (Finset.mem_filter.mp hw).2
    have h1 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hws).1).2
    omega
  rw [second_filter, Finset.card_union_of_disjoint hdis, Nat.add_assoc,
    Finset.card_sdiff_add_card_eq_card hU]

end Problem315.BinaryAssignments

end

end OAI
