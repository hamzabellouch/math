import OAI.MeasureTheory.Falconer.Estimates.ScalarNonporousFraction

namespace OAI

/-! A terminal fiber contributes its full cardinality to every sum
 projection. This is the base case for keeping whole terminal clusters. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_sum_cells_card_left {δ t : ℝ} (hδ : 0 < δ)
    (A B : Finset ℝ) (hB : B.Nonempty)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ |x-y|) :
    A.card ≤ (scalarCells δ (A+B.image (fun y => t*y))).card := by
  classical
  obtain ⟨y,hy⟩ := hB
  let D := A.image (fun x => x+t*y)
  have hDcard : D.card = A.card := Finset.card_image_of_injective _ (add_left_injective (t*y))
  have hDsep : ∀ x ∈ D, ∀ z ∈ D, x ≠ z → δ ≤ |x-z| := by
    intro x hx z hz hxz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    have huv : u ≠ v := fun hh => hxz (by rw [hh])
    simpa only [add_sub_add_right_eq_sub] using hsep u hu v hv huv
  have hsub : D ⊆ A+B.image (fun z => t*z) := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_add.mpr ⟨x,hx,t*y,Finset.mem_image_of_mem _ hy,rfl⟩
  have hc : (scalarCells δ D).card = D.card :=
    Finset.card_image_of_injOn (scalarCells_injective hδ hDsep)
  rw [← hDcard,← hc]
  exact Finset.card_le_card (scalarCells_mono δ hsub)

end Falconer

end OAI
