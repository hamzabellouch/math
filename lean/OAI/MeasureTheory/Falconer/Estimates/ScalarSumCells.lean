import OAI.MeasureTheory.Falconer.Geometry.ProjectionCells
import Mathlib.Combinatorics.Additive.Energy

namespace OAI

/-! Integer-cell comparison for scalar sumsets. These constant-factor
bridges allow the finite additive-combinatorial estimates to be applied
at the same scale as the parameter projections. -/
namespace Falconer
open scoped Pointwise

noncomputable def scalarCells (δ : ℝ) (A : Finset ℝ) : Finset ℤ :=
  A.image fun x => ⌊x/δ⌋

theorem floor_add_carry (u v : ℝ) :
    ⌊u+v⌋ = ⌊u⌋+⌊v⌋ ∨ ⌊u+v⌋ = ⌊u⌋+⌊v⌋+1 := by
  have h1 := Int.le_floor_add u v
  have h2 := Int.le_floor_add_floor u v
  omega

theorem scalarCells_add_subset (δ : ℝ) (A B : Finset ℝ) :
    scalarCells δ (A+B) ⊆ (scalarCells δ A+scalarCells δ B) ∪
      ((scalarCells δ A+scalarCells δ B).image fun z => z+1) := by
  intro z hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hx
  have hmem : ⌊a/δ⌋+⌊b/δ⌋ ∈ scalarCells δ A+scalarCells δ B :=
    Finset.add_mem_add (Finset.mem_image.mpr ⟨a,ha,rfl⟩) (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
  rw [add_div]
  rcases floor_add_carry (a/δ) (b/δ) with h | h
  · exact Finset.mem_union_left _ (h ▸ hmem)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hmem,h.symm⟩)

theorem add_scalarCells_subset (δ : ℝ) (A B : Finset ℝ) :
    scalarCells δ A+scalarCells δ B ⊆ scalarCells δ (A+B) ∪
      ((scalarCells δ (A+B)).image fun z => z-1) := by
  intro z hz
  obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp hz
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
  have hmem : ⌊a/δ+b/δ⌋ ∈ scalarCells δ (A+B) := by
    rw [← add_div]
    exact Finset.mem_image.mpr ⟨a+b,Finset.add_mem_add ha hb,rfl⟩
  rcases floor_add_carry (a/δ) (b/δ) with h | h
  · exact Finset.mem_union_left _ (h ▸ hmem)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hmem,by omega⟩)

theorem scalarCells_add_card (δ : ℝ) (A B : Finset ℝ) :
    (scalarCells δ (A+B)).card ≤ 2*(scalarCells δ A+scalarCells δ B).card := by
  have hb := Finset.card_le_card (scalarCells_add_subset δ A B)
  have hc := Finset.card_union_le (scalarCells δ A+scalarCells δ B)
    ((scalarCells δ A+scalarCells δ B).image fun z => z+1)
  have hi := Finset.card_image_le (s := scalarCells δ A+scalarCells δ B) (f := fun z => z+1)
  omega

theorem add_scalarCells_card (δ : ℝ) (A B : Finset ℝ) :
    (scalarCells δ A+scalarCells δ B).card ≤ 2*(scalarCells δ (A+B)).card := by
  have hb := Finset.card_le_card (add_scalarCells_subset δ A B)
  have hc := Finset.card_union_le (scalarCells δ (A+B))
    ((scalarCells δ (A+B)).image fun z => z-1)
  have hi := Finset.card_image_le (s := scalarCells δ (A+B)) (f := fun z => z-1)
  omega

end Falconer

end OAI
