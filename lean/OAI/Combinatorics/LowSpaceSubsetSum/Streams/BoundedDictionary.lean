import OAI.Combinatorics.LowSpaceSubsetSum.Streams.Trie

namespace OAI

/-!
# Streaming construction of a hard-capacity dictionary

The input is a list of occurrences; equal keys are tested and skipped. The
builder stops at the first new key beyond capacity. Its tree includes the
possibly allocated rejected key, as in the manuscript's implementation.
No Cartesian product or ambient entry set is stored by this procedure.
-/

namespace LowSpaceSubsetSum.BinaryTrie

structure BuildResult where
  tree : Tree
  overflow : Bool
  processed : ℕ

def tick (r : BuildResult) : BuildResult := { r with processed := r.processed + 1 }

def build (C : ℕ) (t : Tree) : List (List Bool) → BuildResult
  | [] => ⟨t, false, 0⟩
  | key :: rest =>
      if contains t key then tick (build C t rest)
      else
        let next := insert t key
        if C < entries next then ⟨next, true, 1⟩
        else tick (build C next rest)

theorem build_processed_le (C : ℕ) (t : Tree) (keys : List (List Bool)) :
    (build C t keys).processed ≤ keys.length := by
  induction keys generalizing t with
  | nil => simp [build]
  | cons key rest ih =>
    simp only [build]
    split
    · simpa [tick] using Nat.add_le_add_right (ih t) 1
    · split
      · simp
      · simpa [tick] using Nat.add_le_add_right (ih (insert t key)) 1

theorem build_hasWidth {C width : ℕ} {t : Tree} {keys : List (List Bool)}
    (ht : HasWidth t width) (hk : ∀ key ∈ keys, key.length = width) :
    HasWidth (build C t keys).tree width := by
  induction keys generalizing t with
  | nil => exact ht
  | cons key rest ih =>
    have hkey := hk key (by simp)
    have hrest : ∀ k ∈ rest, k.length = width := by
      intro k h
      exact hk k (by simp [h])
    simp only [build]
    split
    · exact ih ht hrest
    · split
      · exact insert_hasWidth ht hkey
      · exact ih (insert_hasWidth ht hkey) hrest

theorem build_compact {C : ℕ} {t : Tree} (ht : Compact t)
    (keys : List (List Bool)) : Compact (build C t keys).tree := by
  induction keys generalizing t with
  | nil => exact ht
  | cons key rest ih =>
    simp only [build]
    split
    · exact ih ht
    · split
      · exact insert_compact ht key
      · exact ih (insert_compact ht key)

/-- The capacity is respected on every outcome, including overflow and early
termination. At most one extra key has been allocated. -/
theorem build_entries_le {C width : ℕ} {t : Tree} {keys : List (List Bool)}
    (ht : HasWidth t width) (hk : ∀ key ∈ keys, key.length = width)
    (hcap : entries t ≤ C) : entries (build C t keys).tree ≤ C + 1 := by
  induction keys generalizing t with
  | nil => simpa [build] using hcap.trans (Nat.le_succ C)
  | cons key rest ih =>
    have hkey := hk key (by simp)
    have hrest : ∀ k ∈ rest, k.length = width := by
      intro k h
      exact hk k (by simp [h])
    have he := entries_insert ht hkey
    simp only [build]
    split
    · exact ih ht hrest hcap
    · rename_i hnew
      have hnew' : contains t key = false := Bool.eq_false_iff.mpr hnew
      rw [hnew'] at he
      simp only [Bool.false_eq_true, ↓reduceIte] at he
      split
      · simpa using (show entries (insert t key) ≤ C + 1 by omega)
      · rename_i hfit
        exact ih (insert_hasWidth ht hkey) hrest (by omega)

theorem build_overflow_entries {C width : ℕ} {t : Tree} {keys : List (List Bool)}
    (ht : HasWidth t width) (hk : ∀ key ∈ keys, key.length = width)
    (hcap : entries t ≤ C) (hov : (build C t keys).overflow = true) :
    entries (build C t keys).tree = C + 1 := by
  induction keys generalizing t with
  | nil => simp [build] at hov
  | cons key rest ih =>
    have hkey := hk key (by simp)
    have hrest : ∀ k ∈ rest, k.length = width := by
      intro k h
      exact hk k (by simp [h])
    have he := entries_insert ht hkey
    by_cases hdup : contains t key = true
    · simp only [build, hdup, ↓reduceIte, tick] at hov ⊢
      exact ih ht hrest hcap hov
    · have hnew : contains t key = false := Bool.eq_false_iff.mpr hdup
      rw [hnew] at he
      simp only [Bool.false_eq_true, ↓reduceIte] at he
      by_cases hover : C < entries (insert t key)
      · simp only [build, hnew, Bool.false_eq_true, ↓reduceIte, hover]
        omega
      · simp only [build, hnew, Bool.false_eq_true, ↓reduceIte, hover, tick] at hov ⊢
        exact ih (insert_hasWidth ht hkey) hrest (by omega) hov

/-- A completed build retains exactly the original keys and the input keys,
regardless of how many duplicate occurrences were streamed. -/
theorem build_complete_contains_iff {C width : ℕ} {t : Tree}
    {keys : List (List Bool)} (ht : HasWidth t width)
    (hk : ∀ key ∈ keys, key.length = width)
    (hcomplete : (build C t keys).overflow = false)
    {query : List Bool} (hq : query.length = width) :
    contains (build C t keys).tree query = true ↔
      contains t query = true ∨ query ∈ keys := by
  induction keys generalizing t with
  | nil => simp [build]
  | cons key rest ih =>
    have hkey := hk key (by simp)
    have hrest : ∀ k ∈ rest, k.length = width := by
      intro k h
      exact hk k (by simp [h])
    by_cases hdup : contains t key = true
    · simp only [build, hdup, ↓reduceIte, tick] at hcomplete ⊢
      have hi := ih ht hrest hcomplete
      have hin : query = key → contains t query = true := by
        intro heq
        simpa [heq] using hdup
      rw [hi, List.mem_cons]
      tauto
    · have hnew : contains t key = false := Bool.eq_false_iff.mpr hdup
      by_cases hover : C < entries (insert t key)
      · simp [build, hnew, hover] at hcomplete
      · simp only [build, hnew, Bool.false_eq_true, ↓reduceIte, hover, tick] at hcomplete ⊢
        have hi := ih (insert_hasWidth ht hkey) hrest hcomplete
        rw [hi, contains_insert_iff ht hkey hq, List.mem_cons]
        tauto

/-- Concrete live-trie space, with the first rejected key included. -/
theorem build_nodes_le {C width : ℕ} {t : Tree} {keys : List (List Bool)}
    (ht : HasWidth t width) (hc : Compact t)
    (hk : ∀ key ∈ keys, key.length = width) (hcap : entries t ≤ C) :
    nodes (build C t keys).tree ≤ (width + 1) * (C + 1) := by
  exact (nodes_le_width_mul_entries (build_hasWidth ht hk) (build_compact hc keys)).trans
    (Nat.mul_le_mul_left (width + 1) (build_entries_le ht hk hcap))

end LowSpaceSubsetSum.BinaryTrie

end OAI
