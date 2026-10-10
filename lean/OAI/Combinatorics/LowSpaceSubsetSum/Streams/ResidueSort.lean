import OAI.Combinatorics.LowSpaceSubsetSum.Streams.FilteredRow
import Mathlib.Data.List.Sort

namespace OAI

/-! # Concrete lexicographic residue sorting of the shared right array -/

namespace LowSpaceSubsetSum
namespace ResidueSort

variable {α : Type*}

def relation (w : α → ℤ) (p P : ℤ) (x y : α) : Prop :=
  w x % p < w y % p ∨ w x % p = w y % p ∧ w x % P ≤ w y % P

instance (w : α → ℤ) (p P : ℤ) : DecidableRel (relation w p P) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∧ _))

theorem transitive (w : α → ℤ) (p P : ℤ) :
    ∀ {x y z}, relation w p P x y → relation w p P y z → relation w p P x z := by
  intro x y z hxy hyz
  dsimp only [relation] at *
  omega

theorem total (w : α → ℤ) (p P : ℤ) (x y : α) :
    relation w p P x y ∨ relation w p P y x := by
  dsimp only [relation]
  omega

def sort (xs : Array α) (w : α → ℤ) (p P : ℤ) : Array α :=
  (xs.toList.mergeSort (fun x y => decide (relation w p P x y))).toArray

theorem permutation (xs : Array α) (w : α → ℤ) (p P : ℤ) :
    (sort xs w p P).toList.Perm xs.toList := by
  simpa only [sort, List.toList_toArray] using
    List.mergeSort_perm xs.toList (fun x y => decide (relation w p P x y))

theorem size (xs : Array α) (w : α → ℤ) (p P : ℤ) :
    (sort xs w p P).size = xs.size := by
  have h := (permutation xs w p P).length_eq
  simpa only [Array.length_toList] using h

theorem sorted (xs : Array α) (w : α → ℤ) (p P : ℤ) :
    (sort xs w p P).toList.Pairwise (relation w p P) := by
  simpa only [sort, List.toList_toArray, decide_eq_true_eq] using
    List.pairwise_mergeSort (le := fun x y => decide (relation w p P x y))
      (fun x y z hxy hyz => by
        exact decide_eq_true (transitive w p P (of_decide_eq_true hxy) (of_decide_eq_true hyz)))
      (fun x y => by simpa only [Bool.or_eq_true, decide_eq_true_eq] using total w p P x y)
      xs.toList

theorem index_order (xs : Array α) (w : α → ℤ) (p P : ℤ)
    (i j : Fin (sort xs w p P).size) (hij : i ≤ j) :
    relation w p P (sort xs w p P)[i.val] (sort xs w p P)[j.val] := by
  rcases lt_or_eq_of_le hij with hlt | heq
  · have h := (sorted xs w p P).rel_getElem_of_lt
      (by simpa only [Array.length_toList] using i.isLt)
      (by simpa only [Array.length_toList] using j.isLt) hlt
    simpa only [Array.getElem_toList] using h
  · subst j
    exact Or.inr ⟨rfl, le_rfl⟩

theorem primary (xs : Array α) (w : α → ℤ) (p P : ℤ) :
    FilteredRow.PrimarySorted (sort xs w p P) w p := by
  intro i j hij
  change w (sort xs w p P)[i.val] % p ≤ w (sort xs w p P)[j.val] % p
  have h := index_order xs w p P i j hij
  dsimp only [relation] at h
  omega

theorem secondary (xs : Array α) (w : α → ℤ) (p P : ℤ) :
    FilteredRow.SecondarySorted (sort xs w p P) w p P := by
  intro i j hij heq
  have h := index_order xs w p P i j hij
  dsimp only [relation] at h
  omega

end ResidueSort
end LowSpaceSubsetSum

end OAI
