import Mathlib

namespace OAI

section
section
namespace MetricKMedian.FiniteGraph

variable {I H : Type*} [Fintype H] [DecidableEq I] [DecidableEq H]

noncomputable def incoming (E : H → Finset I) (i : I) : Finset H :=
  Finset.univ.filter (fun h => i ∈ E h)

noncomputable def touching (E : H → Finset I) (S : Finset I) : Finset H :=
  S.biUnion (incoming E)

theorem mem_touching (E : H → Finset I) (S : Finset I) (h : H) :
    h ∈ touching E S ↔ ∃ i ∈ S, i ∈ E h := by
  simp only [touching, Finset.mem_biUnion, incoming, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem touching_card (E : H → Finset I) (S : Finset I) {Δ : ℕ}
    (hin : ∀ i ∈ S, (incoming E i).card ≤ Δ) :
    (touching E S).card ≤ S.card*Δ := by
  apply le_trans (Finset.card_biUnion_le) ?_
  calc
    (∑ i ∈ S, (incoming E i).card) ≤ ∑ _i ∈ S, Δ := Finset.sum_le_sum hin
    _ = S.card*Δ := by simp

noncomputable def conflicts (E : H → Finset I) (balanced : Finset H) (h : H) : Finset H :=
  (touching E (E h) ∩ balanced).erase h

theorem self_not_conflict (E : H → Finset I) (balanced : Finset H) (h : H) :
    h ∉ conflicts E balanced h := by simp [conflicts]

theorem conflicts_card (E : H → Finset I) (balanced : Finset H) (h : H) {Δ : ℕ}
    (hout : (E h).card ≤ Δ) (hin : ∀ i ∈ E h, (incoming E i).card ≤ Δ) :
    (conflicts E balanced h).card ≤ Δ^2 := by
  have hsub : conflicts E balanced h ⊆ touching E (E h) :=
    Finset.Subset.trans (Finset.erase_subset _ _) Finset.inter_subset_left
  calc
    (conflicts E balanced h).card ≤ (touching E (E h)).card := Finset.card_le_card hsub
    _ ≤ (E h).card*Δ := touching_card E (E h) hin
    _ ≤ Δ*Δ := Nat.mul_le_mul_right Δ hout
    _ = Δ^2 := (pow_two Δ).symm

theorem relevant_card {I : Type*} [Fintype I] [DecidableEq I]
    (E : I → Finset I) (S : Finset I) {Δ : ℕ} (hS : S.card ≤ Δ)
    (hin : ∀ i ∈ S, (incoming E i).card ≤ Δ) :
    (S ∪ touching E S).card ≤ Δ^2+Δ := by
  calc
    (S ∪ touching E S).card ≤ S.card+(touching E S).card := Finset.card_union_le _ _
    _ ≤ Δ+Δ*Δ := Nat.add_le_add hS (le_trans (touching_card E S hin) (Nat.mul_le_mul_right Δ hS))
    _ = Δ^2+Δ := by ring

end MetricKMedian.FiniteGraph
end
end

end OAI
