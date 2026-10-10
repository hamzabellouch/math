import Mathlib

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace ConstructionStructure

section RetainedSets

variable {P I : Type*} (S F : I → Set P)

theorem designated_disjoint
    (hsub : ∀ i, F i ⊆ S i)
    (hcompat : ∀ i j, i ≠ j → Disjoint (S i) (F j)) :
    Pairwise (fun i j => Disjoint (F i) (F j)) := by
  intro i j hij
  exact (hcompat i j hij).mono_left (hsub i)

theorem split_inter_retained
    (hsub : ∀ i, F i ⊆ S i)
    (hcompat : ∀ i j, i ≠ j → Disjoint (S i) (F j)) (i : I) :
    S i ∩ ((⋃ j, S j)ᶜ ∪ ⋃ j, F j) = F i := by
  ext p
  constructor
  · rintro ⟨hpS, hpR | hpF⟩
    · exact False.elim (hpR (Set.mem_iUnion.mpr ⟨i, hpS⟩))
    · obtain ⟨j, hpj⟩ := Set.mem_iUnion.mp hpF
      by_cases hij : i = j
      · simpa only [hij] using hpj
      · exact False.elim (Set.disjoint_left.mp (hcompat i j hij) hpS hpj)
  · intro hp
    exact ⟨hsub i hp, Or.inr (Set.mem_iUnion.mpr ⟨i, hp⟩)⟩

theorem designated_slot_unique
    (hcompat : ∀ i j, i ≠ j → Disjoint (S i) (F j))
    {i j : I} {p : P} (hpi : p ∈ F i) (hpj : p ∈ S j) : i = j := by
  by_contra hij
  exact Set.disjoint_left.mp (hcompat j i (Ne.symm hij)) hpj hpi

theorem split_injective
    (hsub : ∀ i, F i ⊆ S i)
    (hcompat : ∀ i j, i ≠ j → Disjoint (S i) (F j))
    (hne : ∀ i, (F i).Nonempty) : Function.Injective S := by
  intro i j hij
  obtain ⟨p, hp⟩ := hne i
  exact designated_slot_unique S F hcompat hp (hij ▸ hsub i hp)

theorem center_not_designated
    (hcompat : ∀ i j, i ≠ j → Disjoint (S i) (F j))
    {i j : I} {p : P} (hij : i ≠ j) (hpi : p ∈ S i) (hpj : p ∈ S j) :
    p ∉ ⋃ k, F k := by
  intro hp
  obtain ⟨k, hpk⟩ := Set.mem_iUnion.mp hp
  have hki := designated_slot_unique S F hcompat hpk hpi
  have hkj := designated_slot_unique S F hcompat hpk hpj
  exact hij (hki.symm.trans hkj)

theorem core_subset_retained {D : Set P} (hSD : (⋃ i, S i) ⊆ D) :
    Dᶜ ⊆ (⋃ i, S i)ᶜ ∪ ⋃ i, F i := by
  intro p hp
  exact Or.inl (fun h => hp (hSD h))

end RetainedSets

section FiniteDesignatedSets

variable {P I : Type*} [DecidableEq P]

theorem designated_union_card (s : Finset I) (F : I → Finset P)
    (hdisj : (s : Set I).Pairwise (fun i j => Disjoint (F i) (F j)))
    (hcard : ∀ i ∈ s, (F i).card = 4) :
    (s.biUnion F).card = 4 * s.card := by
  rw [Finset.card_biUnion hdisj]
  rw [Finset.sum_congr rfl hcard]
  simp [Nat.mul_comm]

theorem partner_card_le_slots (s : Finset I) (F : I → Finset P) (Z : Finset P)
    (hsub : Z ⊆ s.biUnion F)
    (hone : ∀ i ∈ s, (Z ∩ F i).card ≤ 1) : Z.card ≤ s.card := by
  have hcover : Z ⊆ s.biUnion (fun i => Z ∩ F i) := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp (hsub hp)
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_inter.mpr ⟨hp, hpi⟩⟩
  calc
    Z.card ≤ (s.biUnion (fun i => Z ∩ F i)).card := Finset.card_le_card hcover
    _ ≤ ∑ i ∈ s, (Z ∩ F i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ s, 1 := Finset.sum_le_sum hone
    _ = s.card := by simp

end FiniteDesignatedSets

end ConstructionStructure
end Balanced

end OAI
