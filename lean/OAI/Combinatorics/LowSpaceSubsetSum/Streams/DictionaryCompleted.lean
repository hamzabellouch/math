import OAI.Combinatorics.LowSpaceSubsetSum.Streams.RecordedJoin

namespace OAI

/-! # Exact contents whenever a streaming dictionary completes -/

namespace LowSpaceSubsetSum.BinaryTrie

theorem fold_frozen (C : ℕ) (keys : List (List Bool)) (r : BuildResult)
    (ho : r.overflow = true) : keys.foldl (fun r key => feed C key r) r = r := by
  induction keys with
  | nil => rfl
  | cons key keys ih => simpa only [List.foldl_cons, feed_frozen C key r ho] using ih

theorem fold_clear_start (C : ℕ) (keys : List (List Bool)) (r : BuildResult)
    (h : (keys.foldl (fun r key => feed C key r) r).overflow = false) : r.overflow = false := by
  by_cases ho : r.overflow = true
  · rw [fold_frozen C keys r ho, ho] at h
    contradiction
  · exact Bool.eq_false_iff.mpr ho

theorem feed_keySet {C width : ℕ} {r : BuildResult}
    (hr : HasWidth r.tree width) (hc : r.overflow = false)
    (key : List Bool) (hk : key.length = width) :
    keySet (feed C key r).tree = Insert.insert key (keySet r.tree) := by
  by_cases hd : contains r.tree key = true
  · have hm := (mem_keySet r.tree key).mpr hd
    simp only [feed, hc, Bool.false_eq_true, ↓reduceIte, hd, tick]
    exact (Finset.insert_eq_of_mem hm).symm
  · have hf : contains r.tree key = false := Bool.eq_false_iff.mpr hd
    simpa only [feed, hc, hf, Bool.false_eq_true, ↓reduceIte] using keySet_insert hr hk

theorem fold_complete_keySet {C width : ℕ} (keys : List (List Bool)) (r : BuildResult)
    (hr : HasWidth r.tree width) (hk : ∀ key ∈ keys, key.length = width)
    (hc : (keys.foldl (fun r key => feed C key r) r).overflow = false) :
    keySet (keys.foldl (fun r key => feed C key r) r).tree = keySet r.tree ∪ keys.toFinset := by
  induction keys generalizing r with
  | nil => simp
  | cons key keys ih =>
    have hstart := fold_clear_start C (key :: keys) r hc
    have hwidth := (feed_provenance C r hr key (hk key (by simp))).1
    change keySet (keys.foldl (fun r key => feed C key r) (feed C key r)).tree = _
    rw [ih (feed C key r) hwidth (fun q hq => hk q (by simp [hq])) hc,
      feed_keySet hr hstart key (hk key (by simp)), List.toFinset_cons]
    ext q
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto

end LowSpaceSubsetSum.BinaryTrie

namespace LowSpaceSubsetSum.RecordedDictionary

variable {α : Type*}

theorem fold_complete {C width : ℕ} (encode : α → List Bool) (xs : List α)
    (hw : ∀ x ∈ xs, (encode x).length = width)
    (hc : (xs.foldl (fun r x => feed C encode x r) empty).keys.overflow = false) :
    ∀ q, (∃ x ∈ (xs.foldl (fun r x => feed C encode x r) empty).records.toList, encode x = q) ↔
      ∃ x ∈ xs, encode x = q := by
  have hi := fold_invariant (empty_invariant C width encode) xs hw
  rw [fold_keys] at hc
  have hk := BinaryTrie.fold_complete_keySet (C := C) (width := width)
    (xs.map encode) empty.keys (by trivial) (by
      intro key hkey
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hkey
      exact hw x hx) hc
  intro q
  rw [← contains_iff hi q, ← BinaryTrie.mem_keySet, fold_keys, hk]
  simp only [empty, BinaryTrie.keySet, Finset.empty_union, List.mem_toFinset, List.mem_map]

end LowSpaceSubsetSum.RecordedDictionary

end OAI
