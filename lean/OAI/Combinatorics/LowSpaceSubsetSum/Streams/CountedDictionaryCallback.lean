import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CountedRecordedDictionary

namespace OAI

/-! # Counted dictionary callbacks with an intrinsic trie invariant

The executable state carries the proved width/count invariant. Encoding is
computed once per emitted record, and its work plus record copying is included.
-/

namespace LowSpaceSubsetSum.CountedDictionaryCallback

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

def SafeState (C width : ℕ) (encode : α → List Bool × ℕ) :=
  {r : RecordedDictionary.State α //
    RecordedDictionary.Invariant C width (fun x => (encode x).1) r}

def empty (C width : ℕ) (encode : α → List Bool × ℕ) : SafeState C width encode :=
  ⟨RecordedDictionary.empty, RecordedDictionary.empty_invariant _ _ _⟩

def feed (C width : ℕ) (encode : α → List Bool × ℕ)
    (hwidth : ∀ x, (encode x).1.length = width) (cells : α → ℕ)
    (x : α) (r : SafeState C width encode) : SafeState C width encode × ℕ :=
  let code := encode x
  let out := CountedTrie.recordedFeed C (fun _ => code.1) x r.val
  have hv : out.1 = RecordedDictionary.feed C (fun x => (encode x).1) x r.val := by
    change (CountedTrie.recordedFeed C (fun x => (encode x).1) x r.val).1 = _
    exact CountedTrie.recordedFeed_value x r.val r.property (hwidth x)
  (⟨out.1, hv.symm ▸ RecordedDictionary.feed_invariant r.property x (hwidth x)⟩,
    code.2 + out.2 + cells x + 3)

theorem feed_value (C width : ℕ) (encode : α → List Bool × ℕ)
    (hwidth : ∀ x, (encode x).1.length = width) (cells : α → ℕ)
    (x : α) (r : SafeState C width encode) :
    (feed C width encode hwidth cells x r).1.val =
      RecordedDictionary.feed C (fun x => (encode x).1) x r.val :=
  CountedTrie.recordedFeed_value x r.val r.property (hwidth x)

theorem feed_work (C width : ℕ) (encode : α → List Bool × ℕ)
    (hwidth : ∀ x, (encode x).1.length = width) (cells : α → ℕ)
    (K S : ℕ) (hk : ∀ x, (encode x).2 ≤ K) (hs : ∀ x, cells x ≤ S)
    (x : α) (r : SafeState C width encode) :
    (feed C width encode hwidth cells x r).2 ≤ K + S + 2 * width + 14 := by
  have h := CountedTrie.recordedFeed_work C (fun _ : α => (encode x).1) x r.val
  rw [hwidth x] at h
  have he := hk x
  have hc := hs x
  change (encode x).2 + (CountedTrie.recordedFeed C (fun _ : α => (encode x).1) x r.val).2 +
    cells x + 3 ≤ _
  omega

def callback (C width : ℕ) (encode : α → List Bool × ℕ)
    (hwidth : ∀ x, (encode x).1.length = width) (cells : α → ℕ)
    (emit : β → γ → Option α × ℕ) (x : β) (y : γ) (r : SafeState C width encode) :
    (SafeState C width encode × Bool) × ℕ :=
  let found := emit x y
  match found.1 with
  | none => ((r, false), found.2 + 4)
  | some z =>
    let out := feed C width encode hwidth cells z r
    ((out.1, false), found.2 + out.2 + 5)

theorem callback_value (C width : ℕ) (encode : α → List Bool × ℕ)
    (hwidth : ∀ x, (encode x).1.length = width) (cells : α → ℕ)
    (emit : β → γ → Option α × ℕ) (x : β) (y : γ) (r : SafeState C width encode) :
    ((callback C width encode hwidth cells emit x y r).1.1.val,
      (callback C width encode hwidth cells emit x y r).1.2) =
      RecordedDictionary.callback C (fun x => (encode x).1) (fun x y => (emit x y).1) x y r.val := by
  cases he : (emit x y).1 with
  | none => simp only [callback, he, RecordedDictionary.callback]
  | some z => simp only [callback, he, feed_value, RecordedDictionary.callback]

theorem callback_work (C width : ℕ) (encode : α → List Bool × ℕ)
    (hwidth : ∀ x, (encode x).1.length = width) (cells : α → ℕ)
    (emit : β → γ → Option α × ℕ) (K S E : ℕ)
    (hk : ∀ x, (encode x).2 ≤ K) (hs : ∀ x, cells x ≤ S)
    (he : ∀ x y, (emit x y).2 ≤ E)
    (x : β) (y : γ) (r : SafeState C width encode) :
    (callback C width encode hwidth cells emit x y r).2 ≤ E + K + S + 2 * width + 19 := by
  have hemit := he x y
  cases hv : (emit x y).1 with
  | none => simp only [callback, hv]; omega
  | some z =>
    have hf := feed_work C width encode hwidth cells K S hk hs z r
    simp only [callback, hv]
    omega

end LowSpaceSubsetSum.CountedDictionaryCallback

end OAI
