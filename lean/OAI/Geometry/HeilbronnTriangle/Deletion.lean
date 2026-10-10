import Mathlib

namespace OAI


namespace Problem355.Alteration

theorem exists_large_subset_avoiding {α : Type*} (S : Finset α)
    (F : Finset (Finset α)) (hne : ∀ B ∈ F, B.Nonempty) :
    ∃ T : Finset α, T ⊆ S ∧ S.card ≤ T.card + F.card ∧
      ∀ B ∈ F, ¬ B ⊆ T := by
  classical
  let chooseVertex (B : {B // B ∈ F}) : α := (hne B.1 B.2).choose
  have chooseVertex_mem (B : {B // B ∈ F}) : chooseVertex B ∈ B.1 :=
    (hne B.1 B.2).choose_spec
  let D : Finset α := F.attach.image chooseVertex
  have hD : D.card ≤ F.card := by
    calc
      D.card ≤ F.attach.card := Finset.card_image_le
      _ = F.card := Finset.card_attach
  refine ⟨S \ D, Finset.sdiff_subset, ?_, ?_⟩
  · exact (Finset.card_le_card_sdiff_add_card (s := S) (t := D)).trans (Nat.add_le_add_left hD _)
  · intro B hB hBT
    let b : {B // B ∈ F} := ⟨B, hB⟩
    have hbD : chooseVertex b ∈ D := Finset.mem_image.mpr ⟨b, Finset.mem_attach _ _, rfl⟩
    exact (Finset.mem_sdiff.mp (hBT (chooseVertex_mem b))).2 hbD

theorem exists_large_subset_avoiding_sub {α : Type*} (S : Finset α)
    (F : Finset (Finset α)) (hne : ∀ B ∈ F, B.Nonempty) :
    ∃ T : Finset α, T ⊆ S ∧ S.card - F.card ≤ T.card ∧
      ∀ B ∈ F, ¬ B ⊆ T := by
  obtain ⟨T, hTS, hcard, havoid⟩ := exists_large_subset_avoiding S F hne
  exact ⟨T, hTS, by omega, havoid⟩

theorem exists_subset_card_eq_avoiding {α : Type*} (S : Finset α)
    (F : Finset (Finset α)) (hne : ∀ B ∈ F, B.Nonempty)
    (n : ℕ) (hbudget : n + F.card ≤ S.card) :
    ∃ T : Finset α, T ⊆ S ∧ T.card = n ∧ ∀ B ∈ F, ¬ B ⊆ T := by
  obtain ⟨U, hUS, hcard, havoid⟩ := exists_large_subset_avoiding S F hne
  have hnU : n ≤ U.card := by omega
  obtain ⟨T, hTU, hTcard⟩ := Finset.exists_subset_card_eq hnU
  exact ⟨T, hTU.trans hUS, hTcard, fun B hB hBT => havoid B hB (hBT.trans hTU)⟩

end Problem355.Alteration

end OAI
