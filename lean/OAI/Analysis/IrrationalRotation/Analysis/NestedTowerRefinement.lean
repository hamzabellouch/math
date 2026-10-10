import OAI.Analysis.IrrationalRotation.Analysis.NestedReturnSegments
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Data.Set.Image

namespace OAI

namespace Invariant233.NestedTowerRefinement

variable {X ι : Type*} (f : X → X)

def piece (C D : Set X) (r : ℕ) : Set X := D ∩ (f^[r]) ⁻¹' C

theorem cell_eq_iUnion_pieces (C : Set X) (B : ι → Set X) (height : ι → ℕ)
    (hcover : ∀ y : X, ∃ i, ∃ r : Fin (height i), y ∈ (f^[r.val]) '' B i) :
    C = ⋃ i, ⋃ r : Fin (height i), (f^[r.val]) '' piece f C (B i) r.val := by
  apply Set.ext
  intro y
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · intro hy
    obtain ⟨i, r, z, hz, rfl⟩ := hcover y
    exact ⟨i, r, z, ⟨hz, hy⟩, rfl⟩
  · rintro ⟨i, r, z, hz, rfl⟩
    exact hz.2

theorem image_piece_subset (C D : Set X) (r : ℕ) :
    (f^[r]) '' piece f C D r ⊆ (f^[r]) '' D :=
  Set.image_mono Set.inter_subset_left

theorem disjoint_image_pieces {C₁ C₂ D₁ D₂ : Set X} {r s : ℕ}
    (hd : Disjoint ((f^[r]) '' D₁) ((f^[s]) '' D₂)) :
    Disjoint ((f^[r]) '' piece f C₁ D₁ r) ((f^[s]) '' piece f C₂ D₂ s) :=
  hd.mono (image_piece_subset f C₁ D₁ r) (image_piece_subset f C₂ D₂ s)

theorem height_le_of_piece_nonempty {A C D : Set X} {r h H : ℕ}
    (hr : r < H) (hend : ∀ z ∈ D, f^[H] z ∈ A)
    (havoid : ∀ y ∈ C, ∀ t : ℕ, 0 < t → t < h → f^[t] y ∉ A)
    (hne : (piece f C D r).Nonempty) : r + h ≤ H := by
  obtain ⟨z, hzD, hzC⟩ := hne
  exact NestedReturnSegments.return_segment_fits f hr (hend z hzD)
    (havoid (f^[r] z) hzC)

theorem piece_eq_empty_of_height_lt {A C D : Set X} {r h H : ℕ}
    (hr : r < H) (hend : ∀ z ∈ D, f^[H] z ∈ A)
    (havoid : ∀ y ∈ C, ∀ t : ℕ, 0 < t → t < h → f^[t] y ∉ A)
    (hbad : H < r + h) : piece f C D r = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hle := height_le_of_piece_nonempty f hr hend havoid ⟨z, hz⟩
  omega

theorem cell_eq_iUnion_fitting_pieces (A C : Set X) (B : ι → Set X)
    (height : ι → ℕ) (h : ℕ)
    (hcover : ∀ y : X, ∃ i, ∃ r : Fin (height i), y ∈ (f^[r.val]) '' B i)
    (hend : ∀ i z, z ∈ B i → f^[height i] z ∈ A)
    (havoid : ∀ y ∈ C, ∀ t : ℕ, 0 < t → t < h → f^[t] y ∉ A) :
    C = ⋃ i, ⋃ r : Fin (height i), ⋃ (_ : r.val + h ≤ height i),
      (f^[r.val]) '' piece f C (B i) r.val := by
  apply Set.ext
  intro y
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · intro hy
    obtain ⟨i, r, z, hz, rfl⟩ := hcover y
    have hfit : r.val + h ≤ height i :=
      height_le_of_piece_nonempty f r.isLt (hend i) havoid ⟨z, hz, hy⟩
    exact ⟨i, r, hfit, z, ⟨hz, hy⟩, rfl⟩
  · rintro ⟨i, r, hfit, z, hz, rfl⟩
    exact hz.2

theorem measurableSet_piece [MeasurableSpace X] (hf : Measurable f)
    {C D : Set X} (hC : MeasurableSet C) (hD : MeasurableSet D) (r : ℕ) :
    MeasurableSet (piece f C D r) :=
  hD.inter (hC.preimage (hf.iterate r))

end Invariant233.NestedTowerRefinement

end OAI
