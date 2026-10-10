import OAI.Combinatorics.LowSpaceSubsetSum.Storage.TrieCells
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CountedDictionaryCallback

namespace OAI

/-! # Cached dictionary insertion with a live-cell trace

The caller retains the old dictionary and the input record. The trace counts
only the additional trie path, key, array spine and constant local state. It
uses the cached record count and freezes at the first overflowing insertion.
-/

namespace LowSpaceSubsetSum.TrieDictionaryCells

open BinaryTrie

universe u
variable {α : Type u}

def feed (C : ℕ) (key : List Bool) (r : CountedTrie.Cached) :
    (CountedTrie.Cached × ℕ) × ℕ :=
  if r.state.overflow then ((r, 1), 8) else
    let seen := TrieCells.contains r.state.tree key
    if seen.1.1 then ((⟨tick r.state, r.count⟩, seen.1.2 + 3), seen.2 + key.length + 12) else
      let next := TrieCells.insert r.state.tree key
      ((⟨⟨next.1.1, decide (C < r.count + 1), r.state.processed + 1⟩, r.count + 1⟩,
        seen.1.2 + next.1.2 + 6),
        max (seen.2 + key.length + 12) (next.2 + key.length + 16))

theorem feed_value (C : ℕ) (key : List Bool) (r : CountedTrie.Cached) :
    (feed C key r).1 = CountedTrie.feed C key r := by
  simp only [feed, CountedTrie.feed, TrieCells.contains_value, TrieCells.insert_value]
  split
  · rfl
  · split <;> rfl

theorem feed_cells (C : ℕ) (key : List Bool) (r : CountedTrie.Cached) :
    (feed C key r).2 ≤ 6 * key.length + 20 := by
  have hc := TrieCells.contains_cells r.state.tree key
  have hi := TrieCells.insert_cells r.state.tree key
  unfold feed
  split
  · omega
  · dsimp only
    split <;> dsimp only <;> omega

def recordedFeed (C : ℕ) (key : List Bool) (cells : α → ℕ) (x : α)
    (r : RecordedDictionary.State α) : (RecordedDictionary.State α × ℕ) × ℕ :=
  let out := feed C key ⟨r.keys, r.records.size⟩
  ((⟨out.1.1.state, if r.records.size < out.1.1.count then r.records.push x else r.records⟩,
    out.1.2 + 3), out.2 + 2 * r.records.size + cells x + 12)

theorem recordedFeed_value (C : ℕ) (key : List Bool) (cells : α → ℕ) (x : α)
    (r : RecordedDictionary.State α) :
    (recordedFeed C key cells x r).1 = CountedTrie.recordedFeed C (fun _ => key) x r := by
  simp only [recordedFeed, feed_value, CountedTrie.recordedFeed]

theorem recordedFeed_cells (C : ℕ) (key : List Bool) (cells : α → ℕ) (x : α)
    (r : RecordedDictionary.State α) :
    (recordedFeed C key cells x r).2 ≤ 6 * key.length + 2 * r.records.size + cells x + 32 := by
  have h := feed_cells C key ⟨r.keys, r.records.size⟩
  change (feed C key ⟨r.keys, r.records.size⟩).2 + 2 * r.records.size + cells x + 12 ≤ _
  omega

def safeFeed (C width : ℕ) (encode : α → List Bool × ℕ)
    (encodeTrace : α → (List Bool × ℕ) × ℕ) (he : ∀ x, (encodeTrace x).1 = encode x)
    (hwidth : ∀ x, (encode x).1.length = width) (cells : α → ℕ)
    (x : α) (r : CountedDictionaryCallback.SafeState C width encode) :
    (CountedDictionaryCallback.SafeState C width encode × ℕ) × ℕ :=
  let code := encodeTrace x
  let out := recordedFeed C code.1.1 cells x r.val
  have hv : out.1.1 = RecordedDictionary.feed C (fun x => (encode x).1) x r.val := by
    change (recordedFeed C (encodeTrace x).1.1 cells x r.val).1.1 = _
    rw [he x]
    rw [recordedFeed_value]
    change (CountedTrie.recordedFeed C (fun y => (encode y).1) x r.val).1 = _
    exact CountedTrie.recordedFeed_value x r.val r.property (hwidth x)
  ((⟨out.1.1, hv.symm ▸ RecordedDictionary.feed_invariant r.property x (hwidth x)⟩,
    code.1.2 + out.1.2 + cells x + 3),
    max code.2 (out.2 + code.1.1.length + 8))

theorem safeFeed_value (C width : ℕ) (encode : α → List Bool × ℕ)
    (encodeTrace : α → (List Bool × ℕ) × ℕ) (he : ∀ x, (encodeTrace x).1 = encode x)
    (hwidth : ∀ x, (encode x).1.length = width) (cells : α → ℕ)
    (x : α) (r : CountedDictionaryCallback.SafeState C width encode) :
    (safeFeed C width encode encodeTrace he hwidth cells x r).1 =
      CountedDictionaryCallback.feed C width encode hwidth cells x r := by
  apply Prod.ext
  · apply Subtype.ext
    change (recordedFeed C (encodeTrace x).1.1 cells x r.val).1.1 = _
    rw [he x]
    exact congrArg Prod.fst (recordedFeed_value C (encode x).1 cells x r.val)
  · change (encodeTrace x).1.2 + (recordedFeed C (encodeTrace x).1.1 cells x r.val).1.2 + cells x + 3 = _
    rw [he x, recordedFeed_value]
    rfl

theorem safeFeed_cells (C width : ℕ) (encode : α → List Bool × ℕ)
    (encodeTrace : α → (List Bool × ℕ) × ℕ) (he : ∀ x, (encodeTrace x).1 = encode x)
    (hwidth : ∀ x, (encode x).1.length = width) (cells : α → ℕ)
    (E X : ℕ) (hE : ∀ x, (encodeTrace x).2 ≤ E) (hX : ∀ x, cells x ≤ X)
    (x : α) (r : CountedDictionaryCallback.SafeState C width encode) :
    (safeFeed C width encode encodeTrace he hwidth cells x r).2 ≤
      E + 7 * width + 2 * (C + 1) + X + 40 := by
  have hc := recordedFeed_cells C (encodeTrace x).1.1 cells x r.val
  have hx := hX x
  have hr := (RecordedDictionary.storage r.property).1
  have hl : (encodeTrace x).1.1.length = width := by rw [he x, hwidth x]
  have henc := hE x
  change max (encodeTrace x).2
    ((recordedFeed C (encodeTrace x).1.1 cells x r.val).2 + (encodeTrace x).1.1.length + 8) ≤ _
  omega

end LowSpaceSubsetSum.TrieDictionaryCells

end OAI
