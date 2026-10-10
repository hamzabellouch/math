import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace OAI

/-! # Borel selection of the actual finite probe tiles -/

noncomputable section
namespace PolycyclicRecognition

open Set

/-- A measurable finite partition gives a measurable tile index on its
covered set. Empty tiles and an empty covered set cause no difficulty. -/
theorem exists_measurable_probe_tile_index
    {X : Type*} [MeasurableSpace X] {m : ℕ}
    (U : Set X) (tile : Fin m → Set X)
    (hm : ∀ j, MeasurableSet (tile j))
    (hd : Pairwise (fun j k => Disjoint (tile j) (tile k)))
    (hcover : (⋃ j, tile j) = U) :
    ∃ index : U → Fin m, Measurable index ∧
      (∀ x, x.val ∈ tile (index x)) ∧
      ∀ j, index ⁻¹' {j} = Subtype.val ⁻¹' tile j := by
  classical
  have hex (x : U) : ∃ j, x.val ∈ tile j :=
    mem_iUnion.mp (hcover.symm ▸ x.property)
  choose index hindex using hex
  have hiff (x : U) (j : Fin m) : index x = j ↔ x.val ∈ tile j := by
    constructor
    · rintro rfl
      exact hindex x
    · intro hx
      by_contra hne
      exact Set.disjoint_left.mp (hd hne) (hindex x) hx
  have heq (j : Fin m) : index ⁻¹' {j} = Subtype.val ⁻¹' tile j := by
    ext x
    exact hiff x j
  refine ⟨index, measurable_to_countable' (fun j => ?_), hindex, heq⟩
  rw [heq]
  exact measurable_subtype_coe (hm j)

end PolycyclicRecognition

end

end OAI
