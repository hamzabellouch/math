import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {V : Type*} [DecidableEq V]

theorem two_group_resource_card_le (C Ai Bi Aj Bj : Finset V)
    (hAi : Ai ⊆ C) (hBi : Bi ⊆ C) (hAj : Aj ⊆ C) (hBj : Bj ⊆ C)
    (hAiBi : Disjoint Ai Bi) (hAjBj : Disjoint Aj Bj)
    (hAiOther : Disjoint Ai (Aj ∪ Bj))
    (hAjOther : Disjoint Aj (Ai ∪ Bi)) :
    2 * Ai.card + Bi.card + 2 * Aj.card + Bj.card ≤ 2 * C.card := by
  have hAiAj : Disjoint Ai Aj := (Finset.disjoint_union_right.mp hAiOther).1
  have hAiBj : Disjoint Ai Bj := (Finset.disjoint_union_right.mp hAiOther).2
  have hAjBi : Disjoint Aj Bi := (Finset.disjoint_union_right.mp hAjOther).2
  have hlineBi : Disjoint (Ai ∪ Aj) Bi :=
    Finset.disjoint_union_left.mpr ⟨hAiBi, hAjBi⟩
  have hlineBj : Disjoint (Ai ∪ Aj) Bj :=
    Finset.disjoint_union_left.mpr ⟨hAiBj, hAjBj⟩
  have hleft : Ai.card + Aj.card + Bi.card ≤ C.card := by
    have h := Finset.card_le_card (Finset.union_subset (Finset.union_subset hAi hAj) hBi)
    rw [Finset.card_union_of_disjoint hlineBi, Finset.card_union_of_disjoint hAiAj] at h
    exact h
  have hright : Ai.card + Aj.card + Bj.card ≤ C.card := by
    have h := Finset.card_le_card (Finset.union_subset (Finset.union_subset hAi hAj) hBj)
    rw [Finset.card_union_of_disjoint hlineBj, Finset.card_union_of_disjoint hAiAj] at h
    exact h
  omega

theorem two_group_weighted_budget_impossible (s ai bi aj bj n : ℕ)
    (hs : 0 < s)
    (hi : 2 * s ≤ 2 * ai + bi) (hj : 2 * s ≤ 2 * aj + bj)
    (haccount : 2 * ai + bi + 2 * aj + bj ≤ 2 * n)
    (hbudget : n ≤ 2 * (s - 1)) : False := by
  omega

theorem two_group_resource_budget_impossible (C Ai Bi Aj Bj : Finset V)
    (s : ℕ) (hs : 0 < s)
    (hAi : Ai ⊆ C) (hBi : Bi ⊆ C) (hAj : Aj ⊆ C) (hBj : Bj ⊆ C)
    (hAiBi : Disjoint Ai Bi) (hAjBj : Disjoint Aj Bj)
    (hAiOther : Disjoint Ai (Aj ∪ Bj))
    (hAjOther : Disjoint Aj (Ai ∪ Bi))
    (hi : 2 * s ≤ 2 * Ai.card + Bi.card)
    (hj : 2 * s ≤ 2 * Aj.card + Bj.card)
    (hbudget : C.card ≤ 2 * (s - 1)) : False :=
  two_group_weighted_budget_impossible s Ai.card Bi.card Aj.card Bj.card C.card
    hs hi hj
    (two_group_resource_card_le C Ai Bi Aj Bj hAi hBi hAj hBj
      hAiBi hAjBj hAiOther hAjOther)
    hbudget

end RyserCoveringCounterexample.Construction

end OAI
