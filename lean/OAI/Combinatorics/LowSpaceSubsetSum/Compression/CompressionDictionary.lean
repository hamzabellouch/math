import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionSurvival
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.WeightEncoding
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.ProdSigma

namespace OAI

/-!
# The compressed trial's actual lists and bounded solution dictionary

Raw lists enumerate indexed subsets and retain repeated weights. The seven
block lists sort these weights and remove duplicates. Their four generated
pair-sum lists are proof views of the streams; their full products need not
be stored by the implementation.
-/

namespace LowSpaceSubsetSum

theorem compressionRightRaw_lower (n : ℕ) (i : Fin 2) {x : Fin n}
    (hx : x ∈ compressionRightRaw n i) : n - compressionRightRawSize n ≤ x.val := by
  fin_cases i <;> simp [compressionRightRaw, indexInterval] at hx <;> omega

theorem compressionBlock_rightRaw_disjoint (n : ℕ) (i : Fin 7) (j : Fin 2) :
    Disjoint (compressionBlock n i) (compressionRightRaw n j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hxi := (Finset.mem_filter.mp hx).2
  have hlo := compressionRightRaw_lower n j hy
  have hf := compression_layout_feasible n
  have hm := Nat.mul_le_mul_right (compressionHalfSize n)
    (show i.val + 1 ≤ 7 by omega)
  simp only [Nat.add_mul, one_mul] at hm
  omega

theorem compressionLeftRaw_rightRaw_disjoint (n : ℕ) (j : Fin 2) :
    Disjoint (compressionLeftRaw n) (compressionRightRaw n j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hxi := (Finset.mem_filter.mp hx).2
  have hlo := compressionRightRaw_lower n j hy
  have hf := compression_layout_feasible n
  unfold compressionLeftRawSize at hxi
  omega

theorem compressionRightRaw_disjoint (n : ℕ) :
    Disjoint (compressionRightRaw n 0) (compressionRightRaw n 1) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp [compressionRightRaw, indexInterval] at hx hy
  omega

def rawWeightList {n : ℕ} (a : Fin n → ℤ) (V : Finset (Fin n)) : List ℤ :=
  (V.sort (· ≤ ·)).sublists.map (fun indices => weight a indices.toFinset)

theorem mem_rawWeightList {n : ℕ} (a : Fin n → ℤ) (V : Finset (Fin n)) (x : ℤ) :
    x ∈ rawWeightList a V ↔ x ∈ distinctSums a V := by
  constructor
  · intro hx
    obtain ⟨indices, hi, rfl⟩ := List.mem_map.mp hx
    apply (mem_distinctSums _ _ _).mpr
    refine ⟨indices.toFinset, ?_, rfl⟩
    intro i hm
    have hsub := List.mem_sublists.mp hi
    exact (Finset.mem_sort (· ≤ ·)).mp (hsub.subset (List.mem_toFinset.mp hm))
  · intro hx
    obtain ⟨S, hS, rfl⟩ := (mem_distinctSums _ _ _).mp hx
    let indices := (V.sort (· ≤ ·)).filter (fun i => i ∈ S)
    have he : indices.toFinset = S := by
      ext i
      simp only [indices, List.mem_toFinset, List.mem_filter, Finset.mem_sort, decide_eq_true_eq]
      exact ⟨And.right, fun hi => ⟨hS hi, hi⟩⟩
    apply List.mem_map.mpr
    refine ⟨indices, List.mem_sublists.mpr (List.filter_sublist), ?_⟩
    rw [he]

@[simp] theorem rawWeightList_length {n : ℕ} (a : Fin n → ℤ) (V : Finset (Fin n)) :
    (rawWeightList a V).length = 2 ^ V.card := by
  simp [rawWeightList, List.length_sublists]

def compactWeightList {n : ℕ} (a : Fin n → ℤ) (V : Finset (Fin n)) : List ℤ :=
  ((rawWeightList a V).mergeSort (fun x y => decide (x ≤ y))).dedup

theorem mem_compactWeightList {n : ℕ} (a : Fin n → ℤ) (V : Finset (Fin n)) (x : ℤ) :
    x ∈ compactWeightList a V ↔ x ∈ distinctSums a V := by
  rw [compactWeightList, List.mem_dedup,
    (List.mergeSort_perm (rawWeightList a V) (fun x y => decide (x ≤ y))).mem_iff]
  exact mem_rawWeightList a V x

theorem compactWeightList_toFinset {n : ℕ} (a : Fin n → ℤ) (V : Finset (Fin n)) :
    (compactWeightList a V).toFinset = distinctSums a V := by
  ext x
  simp only [List.mem_toFinset, mem_compactWeightList]

@[simp] theorem compactWeightList_length {n : ℕ} (a : Fin n → ℤ) (V : Finset (Fin n)) :
    (compactWeightList a V).length = distinctSumCount a V := by
  have h : (compactWeightList a V).Nodup := List.nodup_dedup _
  rw [← List.toFinset_card_of_nodup h, compactWeightList_toFinset]
  rfl

def pairSumList (xs ys : List ℤ) : List ℤ := (xs.product ys).map (fun p => p.1 + p.2)

theorem mem_pairSumList (xs ys : List ℤ) (z : ℤ) :
    z ∈ pairSumList xs ys ↔ ∃ x ∈ xs, ∃ y ∈ ys, x + y = z := by
  constructor
  · intro h
    obtain ⟨⟨x, y⟩, hp, he⟩ := List.mem_map.mp h
    exact ⟨x, (List.mem_product.mp hp).1, y, (List.mem_product.mp hp).2, he⟩
  · rintro ⟨x, hx, y, hy, he⟩
    exact List.mem_map.mpr ⟨(x, y), List.mem_product.mpr ⟨hx, hy⟩, he⟩

@[simp] theorem pairSumList_length (xs ys : List ℤ) :
    (pairSumList xs ys).length = xs.length * ys.length := by
  rw [pairSumList, List.length_map]
  exact List.length_product xs ys

theorem distinctSums_union_mem_iff {n : ℕ} (a : Fin n → ℤ) (V W : Finset (Fin n))
    (hd : Disjoint V W) (z : ℤ) :
    z ∈ distinctSums a (V ∪ W) ↔
      ∃ x ∈ distinctSums a V, ∃ y ∈ distinctSums a W, x + y = z := by
  constructor
  · intro hz
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp (distinctSums_union_subset a V W hz)
    exact ⟨p.1, (Finset.mem_product.mp hp).1, p.2, (Finset.mem_product.mp hp).2, he⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    obtain ⟨S, hS, rfl⟩ := (mem_distinctSums _ _ _).mp hx
    obtain ⟨T, hT, rfl⟩ := (mem_distinctSums _ _ _).mp hy
    refine (mem_distinctSums _ _ _).mpr ⟨S ∪ T, Finset.union_subset_union hS hT, ?_⟩
    exact weight_union a (hd.mono hS hT)

namespace CompressionSetup

variable {n : ℕ} (R : CompressionSetup n)

theorem blocks_disjoint (e : Equiv.Perm (Fin n)) {i j : Fin 7} (hij : i ≠ j) :
    Disjoint (R.block e i) (R.block e j) :=
  (Finset.disjoint_map e.toEmbedding).mpr (compressionBlock_disjoint n hij)

theorem block_leftRaw_disjoint (e : Equiv.Perm (Fin n)) (i : Fin 7) :
    Disjoint (R.block e i) (R.leftRaw e) :=
  (Finset.disjoint_map e.toEmbedding).mpr (compressionBlock_leftRaw_disjoint n i)

theorem block_rightRaw_disjoint (e : Equiv.Perm (Fin n)) (i : Fin 7) (j : Fin 2) :
    Disjoint (R.block e i) (rightRaw e j) :=
  (Finset.disjoint_map e.toEmbedding).mpr (compressionBlock_rightRaw_disjoint n i j)

theorem rightRaws_disjoint (e : Equiv.Perm (Fin n)) :
    Disjoint (rightRaw e 0) (rightRaw e 1) :=
  (Finset.disjoint_map e.toEmbedding).mpr (compressionRightRaw_disjoint n)

theorem left_groups_disjoint (e : Equiv.Perm (Fin n)) :
    Disjoint (R.groupDomain e 0) (R.groupDomain e 1) := by
  change Disjoint (R.block e 4 ∪ R.block e 5) (R.block e 6 ∪ R.leftRaw e)
  simp only [Finset.disjoint_union_left, Finset.disjoint_union_right]
  repeat' constructor
  · exact R.blocks_disjoint e (i := 4) (j := 6) (by decide)
  · exact R.blocks_disjoint e (i := 5) (j := 6) (by decide)
  · exact R.block_leftRaw_disjoint e 4
  · exact R.block_leftRaw_disjoint e 5

theorem right_groups_disjoint (e : Equiv.Perm (Fin n)) :
    Disjoint (R.groupDomain e 2) (R.groupDomain e 3) := by
  change Disjoint ((R.block e 0 ∪ R.block e 1) ∪ rightRaw e 0)
    ((R.block e 2 ∪ R.block e 3) ∪ rightRaw e 1)
  simp only [Finset.disjoint_union_left, Finset.disjoint_union_right]
  repeat' constructor
  · exact R.blocks_disjoint e (i := 0) (j := 2) (by decide)
  · exact R.blocks_disjoint e (i := 1) (j := 2) (by decide)
  · exact (R.block_rightRaw_disjoint e 2 0).symm
  · exact R.blocks_disjoint e (i := 0) (j := 3) (by decide)
  · exact R.blocks_disjoint e (i := 1) (j := 3) (by decide)
  · exact (R.block_rightRaw_disjoint e 3 0).symm
  · exact R.block_rightRaw_disjoint e 0 1
  · exact R.block_rightRaw_disjoint e 1 1
  · exact rightRaws_disjoint e

theorem groupDomains_disjoint (e : Equiv.Perm (Fin n)) {i j : Fin 4} (hij : i ≠ j) :
    Disjoint (R.groupDomain e i) (R.groupDomain e j) := by
  have hleft : ∀ k : Fin 4, k.val < 2 → R.groupDomain e k ⊆ R.leftDomain e := by
    intro k hk
    rw [R.leftDomain_eq_groups]
    fin_cases k <;> simp_all
  have hright : ∀ k : Fin 4, 2 ≤ k.val → R.groupDomain e k ⊆ R.rightDomain e := by
    intro k hk
    rw [R.rightDomain_eq_groups]
    fin_cases k <;> simp_all
  have hLR : Disjoint (R.leftDomain e) (R.rightDomain e) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 hx
  by_cases hi : i.val < 2 <;> by_cases hj : j.val < 2
  · fin_cases i <;> fin_cases j <;> simp_all [R.left_groups_disjoint e,
      (R.left_groups_disjoint e).symm]
  · exact hLR.mono (hleft i hi) (hright j (by omega))
  · exact hLR.symm.mono (hright i (by omega)) (hleft j hj)
  · fin_cases i <;> fin_cases j <;> simp_all [R.right_groups_disjoint e,
      (R.right_groups_disjoint e).symm]

def storedFirst (e : Equiv.Perm (Fin n)) : Fin 4 → List ℤ :=
  ![compactWeightList R.weights (R.block e 4), compactWeightList R.weights (R.block e 6),
    compactWeightList R.weights (R.block e 0), compactWeightList R.weights (R.block e 2)]

def storedSecond (e : Equiv.Perm (Fin n)) : Fin 4 → List ℤ :=
  ![compactWeightList R.weights (R.block e 5), rawWeightList R.weights (R.leftRaw e),
    pairSumList (compactWeightList R.weights (R.block e 1)) (rawWeightList R.weights (rightRaw e 0)),
    pairSumList (compactWeightList R.weights (R.block e 3)) (rawWeightList R.weights (rightRaw e 1))]

def groupList (e : Equiv.Perm (Fin n)) (i : Fin 4) : List ℤ :=
  pairSumList (R.storedFirst e i) (R.storedSecond e i)

theorem mem_groupList (e : Equiv.Perm (Fin n)) (i : Fin 4) (z : ℤ) :
    z ∈ R.groupList e i ↔ z ∈ R.groupWeights e i := by
  fin_cases i
  · change z ∈ pairSumList (compactWeightList R.weights (R.block e 4))
      (compactWeightList R.weights (R.block e 5)) ↔
        z ∈ distinctSums R.weights (R.block e 4 ∪ R.block e 5)
    rw [mem_pairSumList, distinctSums_union_mem_iff _ _ _ (R.blocks_disjoint e (by decide))]
    simp only [mem_compactWeightList]
  · change z ∈ pairSumList (compactWeightList R.weights (R.block e 6))
      (rawWeightList R.weights (R.leftRaw e)) ↔
        z ∈ distinctSums R.weights (R.block e 6 ∪ R.leftRaw e)
    rw [mem_pairSumList, distinctSums_union_mem_iff _ _ _ (R.block_leftRaw_disjoint e 6)]
    simp only [mem_compactWeightList, mem_rawWeightList]
  · change z ∈ pairSumList (compactWeightList R.weights (R.block e 0))
      (pairSumList (compactWeightList R.weights (R.block e 1))
        (rawWeightList R.weights (rightRaw e 0))) ↔
        z ∈ distinctSums R.weights ((R.block e 0 ∪ R.block e 1) ∪ rightRaw e 0)
    rw [mem_pairSumList, Finset.union_assoc, distinctSums_union_mem_iff _ _ _
      (Finset.disjoint_union_right.mpr ⟨R.blocks_disjoint e (by decide),
        R.block_rightRaw_disjoint e 0 0⟩)]
    simp only [mem_pairSumList, mem_compactWeightList, mem_rawWeightList,
      distinctSums_union_mem_iff _ _ _ (R.block_rightRaw_disjoint e 1 0)]
  · change z ∈ pairSumList (compactWeightList R.weights (R.block e 2))
      (pairSumList (compactWeightList R.weights (R.block e 3))
        (rawWeightList R.weights (rightRaw e 1))) ↔
        z ∈ distinctSums R.weights ((R.block e 2 ∪ R.block e 3) ∪ rightRaw e 1)
    rw [mem_pairSumList, Finset.union_assoc, distinctSums_union_mem_iff _ _ _
      (Finset.disjoint_union_right.mpr ⟨R.blocks_disjoint e (by decide),
        R.block_rightRaw_disjoint e 2 1⟩)]
    simp only [mem_pairSumList, mem_compactWeightList,
      mem_rawWeightList, distinctSums_union_mem_iff _ _ _ (R.block_rightRaw_disjoint e 3 1)]

theorem groupList_toFinset (e : Equiv.Perm (Fin n)) (i : Fin 4) :
    (R.groupList e i).toFinset = R.groupWeights e i := by
  ext z
  exact List.mem_toFinset.trans (R.mem_groupList e i z)

end CompressionSetup

end LowSpaceSubsetSum

end OAI
