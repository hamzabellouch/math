import OAI.MeasureTheory.Falconer.Geometry.ScalarCoverStability

namespace OAI

/-! Counting cells covered by finitely many translated scalar sets. -/
namespace Falconer
open scoped Pointwise

theorem floor_div_near_nat {δ u v : ℝ} (hδ : 0 < δ) (k : ℕ)
    (huv : |u-v| ≤ k*δ) : |⌊u/δ⌋-⌊v/δ⌋| ≤ (k : ℤ)+1 := by
  have hd : |u/δ-v/δ| ≤ (k : ℝ) := by
    rw [← sub_div,abs_div,abs_of_pos hδ]
    exact (div_le_iff₀ hδ).2 huv
  have hu0 := Int.floor_le (u/δ)
  have hu1 := Int.lt_floor_add_one (u/δ)
  have hv0 := Int.floor_le (v/δ)
  have hv1 := Int.lt_floor_add_one (v/δ)
  have he : |(⌊u/δ⌋ : ℝ)-(⌊v/δ⌋ : ℝ)| ≤ (k : ℝ)+1 := by
    rw [abs_le] at hd ⊢
    constructor <;> linarith
  exact_mod_cast he

theorem scalarCells_near_card_nat {δ : ℝ} (hδ : 0 < δ) (A B : Finset ℝ)
    (k : ℕ) (hcover : ∀ a ∈ A, ∃ b ∈ B, |a-b| ≤ k*δ) :
    (scalarCells δ A).card ≤ (2*k+3)*(scalarCells δ B).card := by
  classical
  let I := fun z : ℤ => Finset.Icc (z-((k : ℤ)+1)) (z+((k : ℤ)+1))
  have hsub : scalarCells δ A ⊆ (scalarCells δ B).biUnion I := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨b,hb,hab⟩ := hcover a ha
    apply Finset.mem_biUnion.mpr
    refine ⟨⌊b/δ⌋,Finset.mem_image.mpr ⟨b,hb,rfl⟩,?_⟩
    have hh := floor_div_near_nat hδ k hab
    rw [abs_le] at hh
    apply Finset.mem_Icc.mpr
    omega
  have hI (z : ℤ) : (I z).card = 2*k+3 := by
    dsimp [I]
    rw [Int.card_Icc]
    omega
  calc
    _ ≤ ((scalarCells δ B).biUnion I).card := Finset.card_le_card hsub
    _ ≤ ∑ z ∈ scalarCells δ B, (I z).card := Finset.card_biUnion_le
    _ = _ := by simp [hI,Nat.mul_comm]

theorem scalarCells_translate_cover {δ : ℝ} (hδ : 0 < δ)
    (P F Z : Finset ℝ) (k : ℕ)
    (hcover : ∀ p ∈ P, ∃ f ∈ F, ∃ z ∈ Z, |p-(f+z)| ≤ k*δ) :
    (scalarCells δ P).card ≤ 2*(2*k+3)*F.card*(scalarCells δ Z).card := by
  classical
  have hn := scalarCells_near_card_nat hδ P (F+Z) k (by
    intro p hp
    obtain ⟨f,hf,z,hz,he⟩ := hcover p hp
    exact ⟨f+z,Finset.add_mem_add hf hz,he⟩)
  have hs := scalarCells_add_card δ F Z
  have hc : (scalarCells δ F+scalarCells δ Z).card ≤ F.card*(scalarCells δ Z).card :=
    Finset.card_add_le.trans (Nat.mul_le_mul_right _ (Finset.card_image_le (s := F)))
  calc
    _ ≤ (2*k+3)*(2*(F.card*(scalarCells δ Z).card)) :=
      hn.trans (Nat.mul_le_mul_left _ (hs.trans (Nat.mul_le_mul_left _ hc)))
    _ = _ := by ring

end Falconer

end OAI
