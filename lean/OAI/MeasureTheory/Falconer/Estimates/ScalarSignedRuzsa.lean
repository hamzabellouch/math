import OAI.MeasureTheory.Falconer.Estimates.ScalarRuzsa

namespace OAI

/-! The other sign of the scalar Ruzsa triangle inequality, with the
same rounding loss. -/
namespace Falconer
open scoped Pointwise

 theorem sub_scalarCells_subset (δ : ℝ) (A B : Finset ℝ) :
    scalarCells δ A-scalarCells δ B ⊆ scalarCells δ (A-B) ∪
      ((scalarCells δ (A-B)).image fun z => z+1) := by
  intro z hz
  obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_sub.mp hz
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
  have hmem : ⌊a/δ-b/δ⌋ ∈ scalarCells δ (A-B) := by
    rw [← sub_div]
    exact Finset.mem_image.mpr ⟨a-b,Finset.sub_mem_sub ha hb,rfl⟩
  rcases floor_sub_carry (a/δ) (b/δ) with h | h
  · exact Finset.mem_union_left _ (h ▸ hmem)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hmem,by omega⟩)

 theorem sub_scalarCells_card (δ : ℝ) (A B : Finset ℝ) :
    (scalarCells δ A-scalarCells δ B).card ≤ 2*(scalarCells δ (A-B)).card := by
  have hb := Finset.card_le_card (sub_scalarCells_subset δ A B)
  have hc := Finset.card_union_le (scalarCells δ (A-B))
    ((scalarCells δ (A-B)).image fun z => z+1)
  have hi := Finset.card_image_le (s := scalarCells δ (A-B)) (f := fun z => z+1)
  omega

 theorem scalar_ruzsa_sum_triangle (δ : ℝ) (A B C : Finset ℝ) :
    (scalarCells δ (A+C)).card*(scalarCells δ B).card ≤
      8*(scalarCells δ (B-A)).card*(scalarCells δ (B+C)).card := by
  have hR := Finset.ruzsa_triangle_inequality_add_sub_add
    (scalarCells δ A) (scalarCells δ B) (scalarCells δ C)
  calc
    _ ≤ (2*(scalarCells δ A+scalarCells δ C).card)*(scalarCells δ B).card :=
      Nat.mul_le_mul_right _ (scalarCells_add_card δ A C)
    _ = 2*((scalarCells δ B).card*(scalarCells δ A+scalarCells δ C).card) := by ring
    _ ≤ 2*((scalarCells δ B-scalarCells δ A).card*(scalarCells δ B+scalarCells δ C).card) :=
      Nat.mul_le_mul_left 2 hR
    _ ≤ 2*((2*(scalarCells δ (B-A)).card)*(2*(scalarCells δ (B+C)).card)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul (sub_scalarCells_card δ B A) (add_scalarCells_card δ B C))
    _ = _ := by ring

end Falconer

end OAI
