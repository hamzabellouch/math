import OAI.MeasureTheory.Falconer.Estimates.ScalarSumCells
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa

namespace OAI

/-! The scalar discretized Ruzsa triangle inequality, with the rounding
constant stated explicitly. -/
namespace Falconer
open scoped Pointwise

theorem floor_sub_carry (u v : ℝ) :
    ⌊u-v⌋ = ⌊u⌋-⌊v⌋ ∨ ⌊u-v⌋ = ⌊u⌋-⌊v⌋-1 := by
  have h1 := Int.le_floor_add (u-v) v
  have h2 := Int.le_floor_add_floor (u-v) v
  rw [sub_add_cancel] at h1 h2
  omega

theorem scalarCells_sub_subset (δ : ℝ) (A B : Finset ℝ) :
    scalarCells δ (A-B) ⊆ (scalarCells δ A-scalarCells δ B) ∪
      ((scalarCells δ A-scalarCells δ B).image fun z => z-1) := by
  intro z hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_sub.mp hx
  have hmem : ⌊a/δ⌋-⌊b/δ⌋ ∈ scalarCells δ A-scalarCells δ B :=
    Finset.sub_mem_sub (Finset.mem_image.mpr ⟨a,ha,rfl⟩) (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
  rw [sub_div]
  rcases floor_sub_carry (a/δ) (b/δ) with h | h
  · exact Finset.mem_union_left _ (h ▸ hmem)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hmem,h.symm⟩)

theorem scalarCells_sub_card (δ : ℝ) (A B : Finset ℝ) :
    (scalarCells δ (A-B)).card ≤ 2*(scalarCells δ A-scalarCells δ B).card := by
  have hb := Finset.card_le_card (scalarCells_sub_subset δ A B)
  have hc := Finset.card_union_le (scalarCells δ A-scalarCells δ B)
    ((scalarCells δ A-scalarCells δ B).image fun z => z-1)
  have hi := Finset.card_image_le (s := scalarCells δ A-scalarCells δ B) (f := fun z => z-1)
  omega

theorem scalar_ruzsa_triangle (δ : ℝ) (A B C : Finset ℝ) :
    (scalarCells δ (A-C)).card*(scalarCells δ B).card ≤
      8*(scalarCells δ (A+B)).card*(scalarCells δ (C+B)).card := by
  have hR := Finset.ruzsa_triangle_inequality_sub_add_add
    (scalarCells δ A) (scalarCells δ B) (scalarCells δ C)
  calc
    _ ≤ (2*(scalarCells δ A-scalarCells δ C).card)*(scalarCells δ B).card :=
      Nat.mul_le_mul_right _ (scalarCells_sub_card δ A C)
    _ = 2*((scalarCells δ A-scalarCells δ C).card*(scalarCells δ B).card) := by ring
    _ ≤ 2*((scalarCells δ A+scalarCells δ B).card*(scalarCells δ C+scalarCells δ B).card) :=
      Nat.mul_le_mul_left 2 hR
    _ ≤ 2*((2*(scalarCells δ (A+B)).card)*(2*(scalarCells δ (C+B)).card)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul (add_scalarCells_card δ A B) (add_scalarCells_card δ C B))
    _ = _ := by ring

end Falconer

end OAI
