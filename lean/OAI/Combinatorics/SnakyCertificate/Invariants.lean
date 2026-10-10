import OAI.Combinatorics.SnakyCertificate.Rows

namespace OAI

namespace SnakyCertificate

theorem unionA_subset_unionH (ds : List RowData)
    (h : ∀ d ∈ ds, d.A ⊆ d.H) : unionA ds ⊆ unionH ds := by
  induction ds with
  | nil => simp [unionA, unionH]
  | cons d ds ih =>
    change d.A ∪ unionA ds ⊆ d.H ∪ unionH ds
    exact Finset.union_subset_union (h d (by simp))
      (ih (fun e he => h e (by simp only [List.mem_cons]; exact Or.inr he)))

theorem fold_inter_subset (ss : List (Finset Cell)) (s : Finset Cell) :
    ss.foldr (· ∩ ·) s ⊆ s := by
  induction ss with
  | nil => exact Finset.Subset.refl s
  | cons t ts ih => exact Finset.inter_subset_right.trans ih

theorem commonH_subset_unionH (ds : List RowData) : commonH ds ⊆ unionH ds := by
  cases ds with
  | nil => simp [commonH, unionH]
  | cons d ds =>
    change (ds.map RowData.H).foldr (· ∩ ·) d.H ⊆ d.H ∪ unionH ds
    exact (fold_inter_subset _ _).trans Finset.subset_union_left

theorem forkRow_subset (ds : List RowData) (h : ∀ d ∈ ds, d.A ⊆ d.H) :
    (forkRow ds).A ⊆ (forkRow ds).H := by
  intro p hp
  have hp' : p ∈ unionA ds ∪ commonH ds := Finset.mem_of_mem_erase hp
  exact Finset.mem_insert_of_mem
    ((Finset.union_subset (unionA_subset_unionH ds h) (commonH_subset_unionH ds)) hp')

def RowSubset (d : RowData) : Prop := d.A ⊆ d.H

theorem forkRow_RowSubset (ds : List RowData) (h : ∀ d ∈ ds, RowSubset d) :
    RowSubset (forkRow ds) := forkRow_subset ds h

theorem rowAt_RowSubset (i : ℕ) : RowSubset (rowAt i) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    rw [rowAt]
    split
    · exact Finset.erase_subset _ _
    · refine forkRow_RowSubset
        ((entryAt i).terms.map fun t =>
          placeRow t (if hc : t.child < i then rowAt t.child else emptyRow)) ?_
      intro d hd
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hd
      change (placeRow t (if hc : t.child < i then rowAt t.child else emptyRow)).A ⊆
        (placeRow t (if hc : t.child < i then rowAt t.child else emptyRow)).H
      exact Finset.image_subset_image (by
        split
        · rename_i hc
          exact ih t.child hc
        · exact Finset.Subset.refl ∅)

theorem rowAt_subset (i : ℕ) : (rowAt i).A ⊆ (rowAt i).H := rowAt_RowSubset i

theorem baseRow_origin (i : Fin 6) :
    origin ∈ (baseRow i).H ∧ origin ∉ (baseRow i).A := by
  fin_cases i <;> decide

theorem rowAt_origin (i : ℕ) : origin ∈ (rowAt i).H ∧ origin ∉ (rowAt i).A := by
  rw [rowAt]
  split
  · exact baseRow_origin _
  · simp [forkRow]

theorem rowAt_unique (f : ℕ → RowData) (bound : ℕ)
    (backward : ∀ i, 6 ≤ i → i < bound →
      ∀ t ∈ (entryAt i).terms, t.child < i)
    (equations : ∀ i, i < bound →
      if h : i < 6 then baseRow ⟨i, h⟩ = f i else
        forkRow ((entryAt i).terms.map fun t => placeRow t (f t.child)) = f i) :
    ∀ i, i < bound → rowAt i = f i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    rw [rowAt]
    by_cases hb : i < 6
    · simpa only [dite_eq_left hb] using equations i hi
    · rw [dite_eq_right hb]
      have he := equations i hi
      rw [dite_eq_right hb] at he
      rw [← he]
      apply congrArg forkRow
      apply List.map_congr_left
      intro t ht
      have hc := backward i (by omega) hi t ht
      rw [dite_eq_left hc, ih t.child hc (hc.trans hi)]

end SnakyCertificate

end OAI
