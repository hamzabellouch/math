import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationKeys

namespace OAI

/-! # Retaining generated mask lists in raw-leaf records

Masks are wrapped at the point they are generated. Their finite-set views
are used only by the correctness statements. No canonical sorting
or reconstruction of a finite set is performed for an emitted record.
-/

namespace LowSpaceSubsetSum

namespace IndexedMask

variable {n : ℕ}

private theorem selected_length (xs ys : List (Fin n)) (k : ℕ)
    (hy : ys ∈ (CountedSubsets.select k xs).1) : ys.length ≤ xs.length := by
  rw [CountedSubsets.select_value] at hy
  exact (List.mem_sublistsLen.mp hy).1.length_le

private theorem all_length (xs ys : List (Fin n))
    (hy : ys ∈ (CountedSubsets.all xs).1) : ys.length ≤ xs.length := by
  rw [CountedSubsets.all_value] at hy
  exact (List.mem_sublists.mp hy).length_le

def selected (xs : List (Fin n)) (hx : xs.length ≤ n) (k : ℕ) : List (IndexedMask n) :=
  (CountedSubsets.select k xs).1.attach.map fun y =>
    ⟨y.val, (selected_length xs y.val k y.property).trans hx⟩

def all (xs : List (Fin n)) (hx : xs.length ≤ n) : List (IndexedMask n) :=
  (CountedSubsets.all xs).1.attach.map fun y =>
    ⟨y.val, (all_length xs y.val y.property).trans hx⟩

theorem selected_semantic (xs : List (Fin n)) (hx : xs.length ≤ n) (k : ℕ) :
    (selected xs hx k).map IndexedMask.semantic = (xs.sublistsLen k).map List.toFinset := by
  simp only [selected, List.map_map, Function.comp_def, semantic]
  rw [List.attach_map_val, CountedSubsets.select_value]

theorem all_semantic (xs : List (Fin n)) (hx : xs.length ≤ n) :
    (all xs hx).map IndexedMask.semantic = xs.sublists.map List.toFinset := by
  simp only [all, List.map_map, Function.comp_def, semantic]
  rw [List.attach_map_val, CountedSubsets.all_value]

end IndexedMask

namespace RepresentationLeaf

variable {n : ℕ}

private theorem map_product {α β γ δ : Type*} (f : α → γ) (g : β → δ)
    (xs : List α) (ys : List β) :
    (xs ×ˢ ys).map (Prod.map f g) = xs.map f ×ˢ ys.map g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.product_cons, List.map_append, List.map_map,
      List.map_cons, ih, Function.comp_def, Prod.map]

def storedRecords (L : RepresentationLeaf (Fin n)) : List (LeafRecord n) :=
  if L.topCount ≤ L.top.card ∧ L.localCount ≤ L.mixer.card then
    let t := IndexedMask.selected (domainSort L.top).1
      (by rw [domainSort_length]; simpa using Finset.card_le_univ L.top) L.topCount
    let m := IndexedMask.selected (domainSort L.mixer).1
      (by rw [domainSort_length]; simpa using Finset.card_le_univ L.mixer) L.localCount
    let b := IndexedMask.all (domainSort L.background).1
      (by rw [domainSort_length]; simpa using Finset.card_le_univ L.background)
    ((t ×ˢ m) ×ˢ b).map fun y => ⟨y.1.1, y.1.2, y.2⟩
  else []

theorem storedRecords_semantic (L : RepresentationLeaf (Fin n)) :
    L.storedRecords.map LeafRecord.semantic = L.enumerate := by
  rw [← countedEnumerate_value L]
  unfold storedRecords countedEnumerate
  split_ifs with h
  · simp only [List.map_map]
    change (((IndexedMask.selected _ _ _) ×ˢ (IndexedMask.selected _ _ _)) ×ˢ
      IndexedMask.all _ _).map
      (Prod.map (Prod.map IndexedMask.semantic IndexedMask.semantic) IndexedMask.semantic) = _
    rw [map_product, map_product]
    simp only [IndexedMask.selected_semantic, IndexedMask.all_semantic,
      domainSort_value, CountedSubsets.select_value, CountedSubsets.all_value]
  · rfl

theorem storedRecords_length (L : RepresentationLeaf (Fin n)) :
    L.storedRecords.length = L.occurrences.card := by
  have h := congrArg List.length L.storedRecords_semantic
  simpa only [List.length_map, enumerate_length] using h

theorem storedRecords_mem (L : RepresentationLeaf (Fin n))
    (x : RepresentationLeaf.Occurrence (Fin n)) :
    (∃ y ∈ L.storedRecords, y.semantic = x) ↔ x ∈ L.occurrences := by
  rw [← enumerate_mem, ← storedRecords_semantic]
  exact List.mem_map.symm

end RepresentationLeaf

namespace ResidueSort

variable {α β : Type*}

theorem map_sort (f : α → β) (xs : Array α) (w : β → ℤ) (p P : ℤ) :
    (sort xs (fun x => w (f x)) p P).map f = sort (xs.map f) w p P := by
  apply Array.toList_inj.mp
  simp only [Array.toList_map, sort, List.toList_toArray]
  exact List.map_mergeSort (fun _ _ _ _ => rfl)

end ResidueSort

namespace RepresentationPairData

variable {n : ℕ} (D : RepresentationPairData n)

def leftRecords : Array (LeafRecord n) :=
  (D.left.storedRecords.filter (fun x => D.acceptLeft x.semantic)).toArray

def rawRightRecords : Array (LeafRecord n) :=
  (D.right.storedRecords.filter (fun x => D.acceptRight x.semantic)).toArray

def rightRecords : Array (LeafRecord n) :=
  ResidueSort.sort D.rawRightRecords (fun x => D.wl x.semantic) D.lowModulus D.modulus

theorem leftRecords_semantic : D.leftRecords.map LeafRecord.semantic = D.leftArray := by
  apply Array.toList_inj.mp
  simp only [leftRecords, leftArray, Array.toList_map, List.toList_toArray]
  change (D.left.storedRecords.filter (D.acceptLeft ∘ LeafRecord.semantic)).map LeafRecord.semantic = _
  rw [← List.filter_map, D.left.storedRecords_semantic]

theorem rawRightRecords_semantic :
    D.rawRightRecords.map LeafRecord.semantic = D.rightArray := by
  apply Array.toList_inj.mp
  simp only [rawRightRecords, rightArray, Array.toList_map, List.toList_toArray]
  change (D.right.storedRecords.filter (D.acceptRight ∘ LeafRecord.semantic)).map LeafRecord.semantic = _
  rw [← List.filter_map, D.right.storedRecords_semantic]

theorem rightRecords_semantic : D.rightRecords.map LeafRecord.semantic = D.storedRight := by
  rw [rightRecords, ResidueSort.map_sort, rawRightRecords_semantic]
  rfl

theorem leftRecords_size : D.leftRecords.size = D.leftArray.size := by
  have h := congrArg Array.size D.leftRecords_semantic
  simpa only [Array.size_map] using h

theorem rightRecords_size : D.rightRecords.size = D.storedRight.size := by
  have h := congrArg Array.size D.rightRecords_semantic
  simpa only [Array.size_map] using h

end RepresentationPairData
end LowSpaceSubsetSum

end OAI
