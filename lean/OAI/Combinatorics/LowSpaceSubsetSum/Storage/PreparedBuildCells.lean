import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredPreparationCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PreparedContextCells

namespace OAI

/-! # The complete executed preparation of a shared reader context

The array pair is prepared once and passed by value to the initializer.
The result retains its right array and tournament state; the temporary
left array and component families are dropped after initialization.
-/

namespace LowSpaceSubsetSum.PreparedBuildCells

variable {n : ℕ}

private theorem primary (D : RepresentationParentData n) (F ones zeros : IndexedMask n) (j : Fin 2) :
    FilteredRow.PrimarySorted (StoredPreparationCells.prepare D F ones zeros j).1.1.2
      (fun x => (RepresentationKeys.leafWeight D.input F x).1) D.lowModulus := by
  simp only [StoredPreparationCells.prepare_value, RepresentationStoredArrays.prepare,
    RepresentationKeys.sort_value, RepresentationKeys.leafWeight_value]
  exact ResidueSort.primary _ _ _ _

private theorem secondary (D : RepresentationParentData n) (F ones zeros : IndexedMask n) (j : Fin 2) :
    FilteredRow.SecondarySorted (StoredPreparationCells.prepare D F ones zeros j).1.1.2
      (fun x => (RepresentationKeys.leafWeight D.input F x).1) D.lowModulus D.modulus := by
  simp only [StoredPreparationCells.prepare_value, RepresentationStoredArrays.prepare,
    RepresentationKeys.sort_value, RepresentationKeys.leafWeight_value]
  exact ResidueSort.secondary _ _ _ _

def build (D : RepresentationParentData n) (F : IndexedMask n) (P : StoredRestriction n)
    (_hF : F.semantic = D.signs) (j : Fin 2) :
    (PreparedReaderContext.Context D.input F D.modulus (D.pair j).mode × ℕ) × ℕ :=
  let a := StoredPreparationCells.prepare {D with maskRestriction := P.semantic} F P.ones P.zeros j
  let r := PreparedContextCells.fromArrays D.input F a.1.1.1 a.1.1.2
    D.lowModulus D.modulus (D.pair j).residue
    (primary {D with maskRestriction := P.semantic} F P.ones P.zeros j)
    (secondary {D with maskRestriction := P.semantic} F P.ones P.zeros j)
    D.positive (D.pair j).mode
  ((r.1.1, a.1.2+r.1.2), a.2+r.2+16)

theorem build_value (D : RepresentationParentData n) (F : IndexedMask n) (P : StoredRestriction n)
    (hF : F.semantic = D.signs) (j : Fin 2) :
    (build D F P hF j).1 = PreparedReaderContext.build D F P hF j := by
  simp only [build, PreparedContextCells.fromArrays_value, StoredPreparationCells.prepare_value,
    PreparedReaderContext.build]

theorem build_cells (D : RepresentationParentData n) (F : IndexedMask n) (P : StoredRestriction n)
    (hF : F.semantic = D.signs) (j : Fin 2) (C : ℕ) (hn : 10000 ≤ n)
    (hL : (D.pair j).left.occurrences.card ≤ C)
    (hR : (D.pair j).right.occurrences.card ≤ C) (hC : C ≤ 2^n) :
    (build D F P hF j).2 ≤ inputScale D.input^9*(C+1) := by
  let a := StoredPreparationCells.prepare {D with maskRestriction := P.semantic} F P.ones P.zeros j
  have ha := StoredPreparationCells.prepare_cells {D with maskRestriction := P.semantic}
    F P.ones P.zeros j C hn hL hR hC
  have hsize := RepresentationStoredArrays.prepare_sizes
    {D with maskRestriction := P.semantic} F P.ones P.zeros j
  have hsizes : a.1.1.1.size ≤ C ∧ a.1.1.2.size ≤ C := by
    dsimp only [a]
    rw [StoredPreparationCells.prepare_value]
    exact ⟨hsize.1.trans hL, hsize.2.trans hR⟩
  have hr := PreparedContextCells.fromArrays_cells D.input F a.1.1.1 a.1.1.2
    D.lowModulus D.modulus (D.pair j).residue
    (primary {D with maskRestriction := P.semantic} F P.ones P.zeros j)
    (secondary {D with maskRestriction := P.semantic} F P.ones P.zeros j)
    D.positive (D.pair j).mode C hn hsizes.1 hsizes.2 hC
  have hu : 10000 ≤ inputScale D.input := by unfold inputScale; omega
  have h78 : inputScale D.input^7 ≤ inputScale D.input^8 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hr' := hr.trans (Nat.mul_le_mul_right (C+1) h78)
  have hp : 3*inputScale D.input^8 ≤ inputScale D.input^9 := by
    calc
      _ ≤ inputScale D.input*inputScale D.input^8 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hp' := Nat.mul_le_mul_right (C+1) hp
  simp only [Nat.mul_assoc] at hp'
  have h16 : 16 ≤ inputScale D.input^8*(C+1) := by
    have h := Nat.pow_le_pow_left hu 8
    have h' := Nat.mul_le_mul_left (inputScale D.input^8) (show 1 ≤ C+1 by omega)
    simp only [Nat.mul_one] at h'
    omega
  change a.2+_+16 ≤ _
  change a.2 ≤ inputScale D.input^8*(C+1) at ha
  dsimp only [a] at ha hr' ⊢
  omega

end LowSpaceSubsetSum.PreparedBuildCells

end OAI
