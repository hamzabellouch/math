import OAI.Combinatorics.LowSpaceSubsetSum.Streams.BinaryPivot
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.FilteredStream
import Mathlib.Data.List.FinRange

namespace OAI

/-!
# Stored separator incidence lists and logarithmic interval queries

Each sampled family index occurs once in the stored list, even when two
sampled sets are equal. Preprocessing scans indices in increasing order.
Interval tests make two bounded binary searches in that stored list; they
never scan the family. The counting view is used only in the proofs.
-/

namespace LowSpaceSubsetSum.SeparatorIncidenceTable

variable {α β : Type*}

def table (family : Array β) (compatible : α → β → Bool) (x : α) : Array ℕ :=
  (((List.finRange family.size).filter (fun j => compatible x family[j.val])).map Fin.val).toArray

theorem table_mem (family : Array β) (compatible : α → β → Bool) (x : α) (j : ℕ) :
    j ∈ (table family compatible x).toList ↔
      ∃ h : j < family.size, compatible x family[j] = true := by
  simp only [table, List.toList_toArray, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.isLt, hi⟩
  · rintro ⟨hj, hc⟩
    exact ⟨⟨j, hj⟩, hc, rfl⟩

theorem table_length (family : Array β) (compatible : α → β → Bool) (x : α) :
    (table family compatible x).size ≤ family.size := by
  simpa only [table, List.size_toArray, List.length_map, List.length_finRange] using
    List.length_filter_le (fun j : Fin family.size => compatible x family[j.val])
      (List.finRange family.size)

theorem table_sorted (family : Array β) (compatible : α → β → Bool) (x : α) :
    (table family compatible x).toList.Pairwise (· < ·) := by
  simpa only [table, List.toList_toArray, List.pairwise_map, Fin.lt_def] using
    (List.pairwise_lt_finRange family.size).filter
      (fun j => compatible x family[j.val])

theorem table_monotone (family : Array β) (compatible : α → β → Bool) (x : α) :
    Monotone (fun i : Fin (table family compatible x).size =>
      (table family compatible x)[i.val]) := by
  intro i j hij
  rcases Nat.eq_or_lt_of_le hij with heq | hlt
  · have he : i = j := Fin.ext heq
    rw [he]
  · have h := (table_sorted family compatible x).rel_getElem_of_lt
      (by simpa only [Array.length_toList] using i.isLt)
      (by simpa only [Array.length_toList] using j.isLt) hlt
    simpa only [Array.getElem_toList] using h.le

def lower (a : Array ℕ) (r : ℕ) : ℕ :=
  (BinaryPivot.search (fun i : Fin a.size => decide (a[i.val] < r))
    (FilteredStream.steps a.size)).lo

theorem lower_spec (a : Array ℕ) (hs : Monotone (fun i : Fin a.size => a[i.val]))
    (r : ℕ) (i : Fin a.size) : a[i.val] < r ↔ i.val < lower a r := by
  have hp : BinaryPivot.PrefixPredicate (fun i : Fin a.size => decide (a[i.val] < r)) := by
    intro i j hij hj
    exact decide_eq_true ((hs hij).trans_lt (of_decide_eq_true hj))
  simpa only [lower, decide_eq_true_eq] using
    (BinaryPivot.search_exact _ hp _ (FilteredStream.steps_sufficient a.size)).2 i

theorem lower_bounded (a : Array ℕ) (r : ℕ) : lower a r ≤ a.size :=
  (BinaryPivot.search _ _).ordered.trans (BinaryPivot.search _ _).bounded

def hit (a : Array ℕ) (lo hi : ℕ) : Bool := decide (lower a lo < lower a hi)

theorem hit_iff (a : Array ℕ) (hs : Monotone (fun i : Fin a.size => a[i.val]))
    (lo hi : ℕ) : hit a lo hi = true ↔ ∃ j ∈ a.toList, lo ≤ j ∧ j < hi := by
  simp only [hit, decide_eq_true_eq]
  constructor
  · intro h
    have hin : lower a lo < a.size := h.trans_le (lower_bounded a hi)
    refine ⟨a[lower a lo], Array.getElem_mem_toList hin, ?_, ?_⟩
    · have hspec := lower_spec a hs lo ⟨lower a lo, hin⟩
      dsimp only at hspec
      omega
    · exact (lower_spec a hs hi ⟨lower a lo, hin⟩).mpr h
  · rintro ⟨j, hj, hlo, hhi⟩
    obtain ⟨i, hi', he⟩ := List.mem_iff_getElem.mp hj
    have hin : i < a.size := by simpa using hi'
    rw [Array.getElem_toList] at he
    subst j
    have hl := lower_spec a hs lo ⟨i, hin⟩
    have hh := (lower_spec a hs hi ⟨i, hin⟩).mp hhi
    dsimp only at hl hh
    omega

def count (a : Array ℕ) (lo hi : ℕ) : ℕ :=
  (a.toList.filter (fun j => decide (lo ≤ j ∧ j < hi))).length

theorem hit_count (a : Array ℕ) (hs : Monotone (fun i : Fin a.size => a[i.val]))
    (lo hi : ℕ) : hit a lo hi = true ↔ 0 < count a lo hi := by
  rw [hit_iff a hs, count, List.length_pos_iff_exists_mem]
  simp only [List.mem_filter, decide_eq_true_eq]

theorem count_split (a : Array ℕ) (lo mid hi : ℕ) (hl : lo ≤ mid) (hh : mid ≤ hi) :
    count a lo mid + count a mid hi = count a lo hi := by
  let all := a.toList.filter (fun j => decide (lo ≤ j ∧ j < hi))
  have hleft : all.filter (fun j => decide (j < mid)) =
      a.toList.filter (fun j => decide (lo ≤ j ∧ j < mid)) := by
    dsimp only [all]
    rw [List.filter_filter]
    congr 1
    funext j
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hright : all.filter (fun j => !decide (j < mid)) =
      a.toList.filter (fun j => decide (mid ≤ j ∧ j < hi)) := by
    dsimp only [all]
    rw [List.filter_filter]
    congr 1
    funext j
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq]
    omega
  have h := List.length_eq_length_filter_add (l := all) (fun j => decide (j < mid))
  rw [hleft, hright] at h
  exact h.symm

theorem count_zero_of_not_hit (a : Array ℕ)
    (hs : Monotone (fun i : Fin a.size => a[i.val])) (lo hi : ℕ)
    (h : hit a lo hi = false) : count a lo hi = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hp
  have ht := (hit_count a hs lo hi).mpr hp
  simp [h] at ht

/-- Both compatibility modes are stored for every local bit mask. -/
def preprocess (g : ℕ) (family : Array β) (compatible : Fin (2 ^ g) → β → Bool) :
    Array (Array ℕ) := Array.ofFn (table family compatible)

theorem preprocess_storage (g : ℕ) (family : Array β)
    (compatible : Fin (2 ^ g) → β → Bool) :
    ((preprocess g family compatible).toList.map Array.size).sum ≤ 2 ^ g * family.size := by
  simp only [preprocess, Array.toList_ofFn, List.map_ofFn, List.sum_ofFn]
  calc
    _ ≤ ∑ _ : Fin (2 ^ g), family.size := Finset.sum_le_sum (fun i _ => table_length _ _ i)
    _ = _ := by simp

/-- Two modes on four blocks have the manuscript's stated flat capacity. -/
theorem eight_table_capacity (g : ℕ) (families : Fin 8 → Array β)
    (compatible : Fin 8 → Fin (2 ^ g) → β → Bool)
    (hν : ∀ i, (families i).size ≤ 10 * 2 ^ g + 1) :
    (∑ i : Fin 8, ((preprocess g (families i) (compatible i)).toList.map Array.size).sum) ≤
      8 * 2 ^ g * (10 * 2 ^ g + 1) := by
  calc
    _ ≤ ∑ _ : Fin 8, 2 ^ g * (10 * 2 ^ g + 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact (preprocess_storage g (families i) (compatible i)).trans
        (Nat.mul_le_mul_left _ (hν i))
    _ = _ := by simp; ring

end LowSpaceSubsetSum.SeparatorIncidenceTable

end OAI
