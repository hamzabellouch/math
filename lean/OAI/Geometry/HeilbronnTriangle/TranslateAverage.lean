import Mathlib

namespace OAI


open scoped BigOperators

namespace Problem355.TranslateAverage

variable {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]

omit [Fintype G] in

theorem image_inter_card (S B : Finset G) (a : G) :
    ((S.image (a + ·)) ∩ B).card = (S.filter (fun x => a + x ∈ B)).card := by
  have hset : (S.image (a + ·)) ∩ B =
      (S.filter (fun x => a + x ∈ B)).image (a + ·) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hB⟩
      exact ⟨y, ⟨hy, hB⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hB⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, hB⟩
  rw [hset, Finset.card_image_of_injective]
  exact (Equiv.addLeft a).injective

theorem sum_image_inter_card (S B : Finset G) :
    ∑ a : G, ((S.image (a + ·)) ∩ B).card = S.card * B.card := by
  simp_rw [image_inter_card, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have hin : ∀ x : G, (∑ a : G, if a + x ∈ B then 1 else 0 : ℕ) = B.card := by
    intro x
    calc
      (∑ a : G, if a + x ∈ B then 1 else 0 : ℕ) =
          ∑ a : G, if a ∈ B then 1 else 0 :=
        Equiv.sum_comp (Equiv.addRight x) (fun a => if a ∈ B then (1 : ℕ) else 0)
      _ = B.card := by simp
  simp_rw [hin]
  simp

theorem exists_large_image_inter (S B : Finset G) :
    ∃ a : G, S.card * B.card ≤ Fintype.card G * ((S.image (a + ·)) ∩ B).card := by
  have hsum : (∑ _a : G, S.card * B.card) ≤
      ∑ a : G, Fintype.card G * ((S.image (a + ·)) ∩ B).card := by
    calc
      (∑ _a : G, S.card * B.card) = Fintype.card G * (S.card * B.card) := by simp
      _ = Fintype.card G * (∑ a : G, ((S.image (a + ·)) ∩ B).card) := by
        rw [sum_image_inter_card]
      _ ≤ ∑ a : G, Fintype.card G * ((S.image (a + ·)) ∩ B).card := by
        rw [Finset.mul_sum]
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨a, ha⟩

theorem exists_large_image_inter_real (S B : Finset G) :
    ∃ a : G, (S.card : ℝ) * B.card / Fintype.card G ≤
      (((S.image (a + ·)) ∩ B).card : ℝ) := by
  obtain ⟨a, ha⟩ := exists_large_image_inter S B
  refine ⟨a, (div_le_iff₀ ?_).2 ?_⟩
  · exact_mod_cast Fintype.card_pos
  · have h : (S.card : ℝ) * B.card ≤
        (Fintype.card G : ℝ) * ((S.image (a + ·)) ∩ B).card := by
      exact_mod_cast ha
    simpa only [mul_comm] using h

theorem exists_subset_image_inter (S B : Finset G) :
    ∃ (a : G) (T : Finset G), T ⊆ B ∧ T ⊆ S.image (a + ·) ∧
      (S.card : ℝ) * B.card / Fintype.card G ≤ (T.card : ℝ) := by
  obtain ⟨a, ha⟩ := exists_large_image_inter_real S B
  exact ⟨a, (S.image (a + ·)) ∩ B, Finset.inter_subset_right,
    Finset.inter_subset_left, ha⟩

end Problem355.TranslateAverage

end OAI
