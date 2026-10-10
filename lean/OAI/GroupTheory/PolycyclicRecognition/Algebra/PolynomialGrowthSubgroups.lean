import OAI.GroupTheory.PolycyclicRecognition.Algebra.CayleyWordMaps
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GromovInput

namespace OAI

/-! # Polynomial growth on finitely generated subgroups

The degree is retained: choose one ambient word ball containing the finite
subgroup generators, and count their images in the corresponding scaled ball.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type*} [Group G] [DecidableEq G]

theorem polynomial_growth_subgroup_word_bound
    (S : Finset G) (H : Subgroup G) (T : Finset H) (m : ℕ)
    (hT : ∀ t ∈ T, (t : G) ∈ wordBall S m)
    (C d : ℕ) (hvol : ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d) :
    ∀ n, (wordBall T n).card ≤ (C * (1 + m) ^ d) * (1 + n) ^ d := by
  intro n
  calc
    (wordBall T n).card = ((wordBall T n).image H.subtype).card :=
      (Finset.card_image_of_injective _ H.subtype_injective).symm
    _ ≤ (wordBall S (m * n)).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      exact wordBall_hom_mem_scaled H.subtype S T m hT n ht
    _ ≤ C * (1 + m * n) ^ d := hvol _
    _ ≤ C * ((1 + m) * (1 + n)) ^ d := by
      have : 1 + m * n ≤ (1 + m) * (1 + n) := by nlinarith
      gcongr
    _ = (C * (1 + m) ^ d) * (1 + n) ^ d := by rw [mul_pow]; ring

theorem polynomial_growth_fg_subgroup
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (C d : ℕ)
    (hvol : ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (H : Subgroup G) [Group.FG H] :
    ∃ T : Finset H, (∀ t ∈ T, t⁻¹ ∈ T) ∧
      Subgroup.closure (T : Set H) = ⊤ ∧
      ∃ K : ℕ, ∀ n, (wordBall T n).card ≤ K * (1 + n) ^ d := by
  obtain ⟨T, hTinv, hTgen⟩ := exists_symmetric_finite_generating_set (J := H)
  let m := T.sup (fun t => cayleyWordLength S hS hgen (t : G))
  have hT (t : H) (ht : t ∈ T) : (t : G) ∈ wordBall S m :=
    (cayleyWordLength_le_iff S hS hgen t m).mp (Finset.le_sup (f := fun t : H => cayleyWordLength S hS hgen (t : G)) ht)
  exact ⟨T, hTinv, hTgen, C * (1 + m) ^ d,
    polynomial_growth_subgroup_word_bound S H T m hT C d hvol⟩


theorem polynomial_growth_fg_injective
    {H : Type*} [Group H] [DecidableEq H] [Group.FG H]
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (C d : ℕ)
    (hvol : ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (f : H →* G) (hf : Function.Injective f) :
    ∃ T : Finset H, (∀ t ∈ T, t⁻¹ ∈ T) ∧
      Subgroup.closure (T : Set H) = ⊤ ∧
      ∃ K : ℕ, ∀ n, (wordBall T n).card ≤ K * (1 + n) ^ d := by
  obtain ⟨T, hTinv, hTgen⟩ := exists_symmetric_finite_generating_set (J := H)
  let m := T.sup (fun t => cayleyWordLength S hS hgen (f t))
  have hT (t : H) (ht : t ∈ T) : f t ∈ wordBall S m :=
    (cayleyWordLength_le_iff S hS hgen (f t) m).mp
      (Finset.le_sup (f := fun t : H => cayleyWordLength S hS hgen (f t)) ht)
  refine ⟨T, hTinv, hTgen, C * (1 + m) ^ d, fun n => ?_⟩
  calc
    (wordBall T n).card = ((wordBall T n).image f).card :=
      (Finset.card_image_of_injective _ hf).symm
    _ ≤ (wordBall S (m * n)).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      exact wordBall_hom_mem_scaled f S T m hT n ht
    _ ≤ C * (1 + m * n) ^ d := hvol _
    _ ≤ C * ((1 + m) * (1 + n)) ^ d := by
      have : 1 + m * n ≤ (1 + m) * (1 + n) := by nlinarith
      gcongr
    _ = (C * (1 + m) ^ d) * (1 + n) ^ d := by rw [mul_pow]; ring

end PolycyclicRecognition

end

end OAI
