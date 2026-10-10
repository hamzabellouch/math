import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationStoredRecords
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredSort

namespace OAI

/-! # Actual costed residue sorting of stored leaf records -/

namespace LowSpaceSubsetSum.RepresentationKeys

variable {n : ℕ}

def compare (I : Instance n) (F : IndexedMask n) (p P : ℤ)
    (x y : LeafRecord n) : Bool × ℕ :=
  let a := leafWeight I F x
  let b := leafWeight I F y
  (decide (a.1 % p < b.1 % p ∨ a.1 % p = b.1 % p ∧ a.1 % P ≤ b.1 % P),
    a.2 + b.2 + 6)

theorem compare_value (I : Instance n) (F : IndexedMask n) (p P : ℤ)
    (x y : LeafRecord n) :
    (compare I F p P x y).1 = decide (ResidueSort.relation
      (fun x : LeafRecord n => RepresentationLeaf.occurrenceWeight
        (flip (fun i => (I.values i : ℤ)) F.semantic) x.semantic) p P x y) := by
  simp only [compare, leafWeight_value, ResidueSort.relation]
  rfl

theorem compare_work (I : Instance n) (F : IndexedMask n) (p P : ℤ)
    (x y : LeafRecord n) : (compare I F p P x y).2 ≤ 70 * (n + 1) ^ 2 := by
  have hx := leafWeight_work I F x
  have hy := leafWeight_work I F y
  have h1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  change _ + _ + 6 ≤ _
  omega

private theorem comparator_polynomial {n u : ℕ} (hn : n + 1 ≤ u) (hu : 10000 ≤ u) :
    70 * (n + 1) ^ 2 ≤ u ^ 3 := by
  have hs := Nat.pow_le_pow_left hn 2
  have hm := Nat.mul_le_mul_right (u ^ 2) (show 70 ≤ u by omega)
  nlinarith only [hs, hm]

theorem compare_scale (I : Instance n) (F : IndexedMask n) (p P : ℤ)
    (x y : LeafRecord n) (hn : 10000 ≤ n) :
    (compare I F p P x y).2 ≤ inputScale I ^ 3 := by
  have hnu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  exact (compare_work I F p P x y).trans (comparator_polynomial hnu (by omega))

def sort (I : Instance n) (F : IndexedMask n) (p P : ℤ)
    (xs : Array (LeafRecord n)) : Array (LeafRecord n) × ℕ :=
  let out := MeasuredSort.sort (compare I F p P) xs.toList
  (out.1.toArray, out.2 + xs.size)

theorem sort_value (I : Instance n) (F : IndexedMask n) (p P : ℤ)
    (xs : Array (LeafRecord n)) :
    (sort I F p P xs).1 = ResidueSort.sort xs
      (fun x : LeafRecord n => RepresentationLeaf.occurrenceWeight
        (flip (fun i => (I.values i : ℤ)) F.semantic) x.semantic) p P := by
  simp only [sort, MeasuredSort.sort_value, compare_value, ResidueSort.sort]

theorem sort_work (I : Instance n) (F : IndexedMask n) (p P : ℤ)
    (xs : Array (LeafRecord n)) (hn : 10000 ≤ n) (hsize : xs.size ≤ 2 ^ n) :
    (sort I F p P xs).2 ≤
      (inputScale I ^ 3 + 1) * ((6 * n + 1) * xs.size + 1) + xs.size := by
  have h := MeasuredSort.sort_work (compare I F p P) (inputScale I ^ 3)
    (fun x y => compare_scale I F p P x y hn) xs.toList n (by simpa using hsize)
  exact Nat.add_le_add_right h xs.size

private theorem sort_polynomial {n u N C : ℕ} (hnu : n + 1 ≤ u)
    (hu : 10000 ≤ u) (hN : N ≤ C) :
    (u ^ 3 + 1) * ((6 * n + 1) * N + 1) + N ≤ u ^ 5 * (C + 1) := by
  have hu1 : 1 ≤ u ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hA : u ^ 3 + 1 ≤ 2 * u ^ 3 := by omega
  have hB : (6 * n + 1) * N + 1 ≤ 7 * u * (C + 1) := by
    have hb := Nat.mul_le_mul (show 6 * n + 1 ≤ 7 * u by omega) hN
    have hp : 1 ≤ 7 * u := by omega
    nlinarith only [hb, hp]
  have hm := Nat.mul_le_mul hA hB
  have hN' : N ≤ u ^ 4 * (C + 1) := by
    have hp : 1 ≤ u ^ 4 := Nat.one_le_pow _ _ (by omega)
    have hb := Nat.mul_le_mul_right (C + 1) hp
    omega
  have hpow : 15 * u ^ 4 ≤ u ^ 5 := by
    calc
      _ ≤ u * u ^ 4 := Nat.mul_le_mul_right _ (show 15 ≤ u by omega)
      _ = _ := (pow_succ' u 4).symm
  have ht := Nat.mul_le_mul_right (C + 1) hpow
  nlinarith only [hm, hN', ht]

theorem sort_scale (I : Instance n) (F : IndexedMask n) (p P : ℤ)
    (xs : Array (LeafRecord n)) (hn : 10000 ≤ n) {C : ℕ}
    (hsize : xs.size ≤ C) (hC : C ≤ 2 ^ n) :
    (sort I F p P xs).2 ≤ inputScale I ^ 5 * (C + 1) := by
  have hnu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  exact (sort_work I F p P xs hn (hsize.trans hC)).trans
    (sort_polynomial hnu (by omega) hsize)

theorem sort_parent_value (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) :
    ((sort D.input F D.lowModulus D.modulus (D.pair j).rawRightRecords).1).map
      LeafRecord.semantic = (D.pair j).storedRight := by
  rw [sort_value, hF]
  change (ResidueSort.sort (D.pair j).rawRightRecords
    (fun x => (D.pair j).wl x.semantic) D.lowModulus D.modulus).map LeafRecord.semantic = _
  exact (D.pair j).rightRecords_semantic

end LowSpaceSubsetSum.RepresentationKeys

end OAI
