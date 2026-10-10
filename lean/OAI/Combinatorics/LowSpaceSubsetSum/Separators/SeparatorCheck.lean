import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorExpectation

namespace OAI

/-!
# Four-block weighted disjointness check

A top mask has four local blocks of `g` indices. The check preprocesses both
compatibility tables, traverses the useful tuples without storing them, and
uses the first-match weight search at each terminal branch.
-/

namespace LowSpaceSubsetSum.SeparatorCheck

open SeparatorBlocks SeparatorIncidenceTable

variable {g : ℕ}

abbrev Record (g : ℕ) := Entry (Fin 4 × Fin g)

def localMask (i : Fin 4) (S : Finset (Fin 4 × Fin g)) : Finset (Fin g) :=
  Finset.univ.filter (fun j => (i, j) ∈ S)

@[simp] theorem localMask_mem (i : Fin 4) (S : Finset (Fin 4 × Fin g)) (j : Fin g) :
    j ∈ localMask i S ↔ (i, j) ∈ S := by simp [localMask]

def blocks (families : Fin 4 → Array (Finset (Fin g))) : List (Block (Record g) (Record g)) :=
  List.ofFn (fun i : Fin 4 => ofFamily (families i)
    (fun x : Record g => localMask i x.mask) (fun y : Record g => localMask i y.mask))

def run (n : ℕ) (families : Fin 4 → Array (Finset (Fin g))) (target : ℤ)
    (xs ys : List (Record g)) : SeparatorTraversal.Result :=
  check n Entry.value Entry.value target (blocks families) xs ys

theorem ofFamily_pair_good (family : Array (Finset (Fin g)))
    (mask₁ mask₂ : Record g → Finset (Fin g)) (x y : Record g) :
    (∃ j < (ofFamily family mask₁ mask₂).size,
      j ∈ ((ofFamily family mask₁ mask₂).left x).toList ∧
      j ∈ ((ofFamily family mask₁ mask₂).right y).toList) ↔
    ∃ j : Fin family.size, mask₁ x ⊆ family[j.val] ∧ Disjoint (mask₂ y) family[j.val] := by
  simp only [ofFamily, SeparatorStoredMasks.containsList_eq, SeparatorStoredMasks.avoidsList_eq]
  constructor
  · rintro ⟨j, hj, hl, hr⟩
    obtain ⟨_, hl⟩ := (table_mem _ _ _ _).mp hl
    obtain ⟨_, hr⟩ := (table_mem _ _ _ _).mp hr
    exact ⟨⟨j, hj⟩, of_decide_eq_true hl, of_decide_eq_true hr⟩
  · rintro ⟨j, hl, hr⟩
    exact ⟨j.val, j.isLt, (table_mem _ _ _ _).mpr ⟨j.isLt, decide_eq_true hl⟩,
      (table_mem _ _ _ _).mpr ⟨j.isLt, decide_eq_true hr⟩⟩

def Covered (families : Fin 4 → Array (Finset (Fin g))) (x y : Record g) : Prop :=
  ∀ i, ∃ j : Fin (families i).size,
    localMask i x.mask ⊆ (families i)[j.val] ∧
      Disjoint (localMask i y.mask) (families i)[j.val]

theorem pairGood_iff (families : Fin 4 → Array (Finset (Fin g))) (x y : Record g) :
    PairGood (blocks families) x y ↔ Covered families x y := by
  simp only [PairGood, blocks, List.mem_ofFn, forall_exists_index,
    forall_apply_eq_imp_iff, ofFamily_pair_good, Covered]

theorem correct (n : ℕ) (families : Fin 4 → Array (Finset (Fin g))) (target : ℤ)
    (xs ys : List (Record g)) (hsize : xs.length + ys.length ≤ 2 ^ n) :
    (run n families target xs ys).accepted = true ↔
      ∃ x ∈ xs, ∃ y ∈ ys, Covered families x y ∧ x.value + y.value = target := by
  simpa only [run, pairGood_iff] using
    SeparatorBlocks.correct n Entry.value Entry.value target (blocks families) xs ys hsize

theorem covered_disjoint (families : Fin 4 → Array (Finset (Fin g))) (x y : Record g)
    (h : Covered families x y) : Disjoint x.mask y.mask := by
  apply Finset.disjoint_left.mpr
  rintro ⟨i, j⟩ hx hy
  obtain ⟨k, hl, hr⟩ := h i
  exact Finset.disjoint_left.mp hr ((localMask_mem i y.mask j).mpr hy)
    (hl ((localMask_mem i x.mask j).mpr hx))

theorem sound (n : ℕ) (families : Fin 4 → Array (Finset (Fin g))) (target : ℤ)
    (xs ys : List (Record g)) (hsize : xs.length + ys.length ≤ 2 ^ n)
    (hyes : (run n families target xs ys).accepted = true) :
    ∃ x ∈ xs, ∃ y ∈ ys, Disjoint x.mask y.mask ∧ x.value + y.value = target := by
  obtain ⟨x, hx, y, hy, hc, hw⟩ := (correct _ _ _ _ _ hsize).mp hyes
  exact ⟨x, hx, y, hy, covered_disjoint families x y hc, hw⟩

theorem finds_fixed_pair (n : ℕ) (families : Fin 4 → Array (Finset (Fin g))) (target : ℤ)
    (xs ys : List (Record g)) (hsize : xs.length + ys.length ≤ 2 ^ n)
    (x y : Record g) (hx : x ∈ xs) (hy : y ∈ ys)
    (hw : x.value + y.value = target) (hc : Covered families x y) :
    (run n families target xs ys).accepted = true :=
  (correct _ _ _ _ _ hsize).mpr ⟨x, hx, y, hy, hc, hw⟩

theorem peak_le (n : ℕ) (families : Fin 4 → Array (Finset (Fin g))) (target : ℤ)
    (xs ys : List (Record g)) :
    (run n families target xs ys).peak ≤ peakBound n (blocks families) :=
  SeparatorBlocks.peak_le _ _ _ _ _ _ _

theorem peak_capacity (n C : ℕ) (families : Fin 4 → Array (Finset (Fin g)))
    (target : ℤ) (xs ys : List (Record g))
    (hsize : xs.length + ys.length ≤ C) (hC : C ≤ 2 ^ n) :
    (run n families target xs ys).peak ≤ capacityPeak n C (blocks families) :=
  SeparatorBlocks.peak_capacity _ _ _ _ _ _ _ _ hsize hC

end LowSpaceSubsetSum.SeparatorCheck

end OAI
