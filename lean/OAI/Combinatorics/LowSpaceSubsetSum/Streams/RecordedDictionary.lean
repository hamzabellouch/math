import OAI.Combinatorics.LowSpaceSubsetSum.Streams.DictionaryPrefixes
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.DictionaryProvenance
import OAI.Combinatorics.LowSpaceSubsetSum.Search.StoppedStreamJoin

namespace OAI

/-! # Bounded dictionaries with an actual array of retained records -/

namespace LowSpaceSubsetSum.RecordedDictionary

universe u
variable {α : Type u}

structure State (α : Type u) where
  keys : BinaryTrie.BuildResult
  records : Array α

def empty : State α := ⟨⟨.empty, false, 0⟩, #[]⟩

/-- The first rejected record is retained, as is its newly allocated trie key.
Further callbacks freeze both structures. -/
def feed (C : ℕ) (encode : α → List Bool) (x : α) (r : State α) : State α :=
  ⟨BinaryTrie.feed C (encode x) r.keys,
    if r.keys.overflow || BinaryTrie.contains r.keys.tree (encode x)
    then r.records else r.records.push x⟩

@[simp] theorem feed_keys (C : ℕ) (encode : α → List Bool) (x : α) (r : State α) :
    (feed C encode x r).keys = BinaryTrie.feed C (encode x) r.keys := rfl

structure Invariant (C width : ℕ) (encode : α → List Bool) (r : State α) : Prop where
  safe : BinaryTrie.Safe C width r.keys
  keys_eq : BinaryTrie.keySet r.keys.tree = (r.records.toList.map encode).toFinset
  size_eq : r.records.size = BinaryTrie.entries r.keys.tree

theorem empty_invariant (C width : ℕ) (encode : α → List Bool) :
    Invariant C width encode empty := by
  exact ⟨BinaryTrie.empty_safe C width, rfl, rfl⟩

theorem feed_invariant {C width : ℕ} {encode : α → List Bool} {r : State α}
    (hr : Invariant C width encode r) (x : α) (hx : (encode x).length = width) :
    Invariant C width encode (feed C encode x r) := by
  refine ⟨BinaryTrie.feed_safe hr.safe (encode x) hx, ?_, ?_⟩
  · by_cases ho : r.keys.overflow = true
    · simpa only [feed, ho, Bool.true_or, ↓reduceIte,
        BinaryTrie.feed_frozen C (encode x) r.keys ho] using hr.keys_eq
    have hoc : r.keys.overflow = false := Bool.eq_false_iff.mpr ho
    by_cases hd : BinaryTrie.contains r.keys.tree (encode x) = true
    · simpa only [feed, hoc, hd, Bool.false_or, ↓reduceIte,
        BinaryTrie.feed, Bool.false_eq_true, BinaryTrie.tick] using hr.keys_eq
    have hdc : BinaryTrie.contains r.keys.tree (encode x) = false := Bool.eq_false_iff.mpr hd
    simp only [feed, hoc, hdc, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
      BinaryTrie.feed, Array.toList_push, List.map_append, List.map_cons,
      List.map_nil, List.toFinset_append, List.toFinset_cons, List.toFinset_nil]
    rw [BinaryTrie.keySet_insert hr.safe.hasWidth hx, hr.keys_eq]
    ext q
    simp
  · by_cases ho : r.keys.overflow = true
    · simpa only [feed, ho, Bool.true_or, ↓reduceIte,
        BinaryTrie.feed_frozen C (encode x) r.keys ho] using hr.size_eq
    have hoc : r.keys.overflow = false := Bool.eq_false_iff.mpr ho
    by_cases hd : BinaryTrie.contains r.keys.tree (encode x) = true
    · simpa only [feed, hoc, hd, Bool.false_or, ↓reduceIte,
        BinaryTrie.feed, Bool.false_eq_true, BinaryTrie.tick] using hr.size_eq
    have hdc : BinaryTrie.contains r.keys.tree (encode x) = false := Bool.eq_false_iff.mpr hd
    simp only [feed, hoc, hdc, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
      BinaryTrie.feed, Array.size_push]
    rw [BinaryTrie.entries_insert hr.safe.hasWidth hx, hdc]
    simpa using hr.size_eq

/-- Every stopped state stores at most the capacity plus the rejected record. -/
theorem storage {C width : ℕ} {encode : α → List Bool} {r : State α}
    (hr : Invariant C width encode r) :
    r.records.size ≤ C + 1 ∧ BinaryTrie.nodes r.keys.tree ≤ (width + 1) * (C + 1) := by
  exact ⟨hr.size_eq.trans_le hr.safe.bound,
    (BinaryTrie.nodes_le_width_mul_entries hr.safe.hasWidth hr.safe.compact).trans
      (Nat.mul_le_mul_left _ hr.safe.bound)⟩

theorem contains_iff {C width : ℕ} {encode : α → List Bool} {r : State α}
    (hr : Invariant C width encode r) (q : List Bool) :
    BinaryTrie.contains r.keys.tree q = true ↔ ∃ x ∈ r.records.toList, encode x = q := by
  rw [← BinaryTrie.mem_keySet, hr.keys_eq, List.mem_toFinset, List.mem_map]

theorem feed_provenance (C : ℕ) (encode : α → List Bool) (x : α) (r : State α)
    (P : α → Prop) (hr : ∀ y ∈ r.records.toList, P y) (hx : P x) :
    ∀ y ∈ (feed C encode x r).records.toList, P y := by
  intro y hy
  simp only [feed] at hy
  split at hy
  · exact hr y hy
  · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact hr y hy
    · exact hx

theorem fold_invariant {C width : ℕ} {encode : α → List Bool} {r : State α}
    (hr : Invariant C width encode r) (xs : List α)
    (hw : ∀ x ∈ xs, (encode x).length = width) :
    Invariant C width encode (xs.foldl (fun r x => feed C encode x r) r) := by
  induction xs generalizing r with
  | nil => exact hr
  | cons x xs ih =>
    exact ih (feed_invariant hr x (hw x (by simp))) (fun y hy => hw y (by simp [hy]))

theorem fold_keys (C : ℕ) (encode : α → List Bool) (xs : List α) (r : State α) :
    (xs.foldl (fun r x => feed C encode x r) r).keys =
      (xs.map encode).foldl (fun r key => BinaryTrie.feed C key r) r.keys := by
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih => exact ih (feed C encode x r)

/-- A cardinality bound concerns distinct keys, rather than repeated callbacks.
When it holds, every supplied record has its key retained in the array. -/
theorem fold_fits {C width : ℕ} (encode : α → List Bool) (xs : List α)
    (U : Finset (List Bool)) (hwidth : ∀ q ∈ U, q.length = width)
    (hcap : U.card ≤ C) (hkeys : ∀ x ∈ xs, encode x ∈ U) :
    let r := xs.foldl (fun r x => feed C encode x r) empty
    r.keys.overflow = false ∧
      ∀ q, (∃ x ∈ r.records.toList, encode x = q) ↔ ∃ x ∈ xs, encode x = q := by
  have hw : ∀ x ∈ xs, (encode x).length = width := fun x hx => hwidth _ (hkeys x hx)
  have hi := fold_invariant (empty_invariant C width encode) xs hw
  have hf := BinaryTrie.fold_fits (r := ⟨.empty, false, 0⟩) rfl
    (width := width) (by trivial) hwidth (by simp [BinaryTrie.keySet]) hcap
    (xs.map encode) (by
      intro q hq
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
      exact hkeys x hx)
  dsimp only
  refine ⟨?_, ?_⟩
  · rw [fold_keys]
    exact hf.1
  · intro q
    rw [← contains_iff hi q, ← BinaryTrie.mem_keySet, fold_keys]
    dsimp only [empty]
    rw [hf.2.1]
    simp only [BinaryTrie.keySet, Finset.empty_union, List.mem_toFinset, List.mem_map]

/-- The option-valued emitter applies local overlap and prefix checks before
an entry is retained. A rejected tuple consumes no dictionary space. -/
def callback {β γ : Type*} (C : ℕ) (encode : α → List Bool)
    (emit : β → γ → Option α) (x : β) (y : γ) (r : State α) : State α × Bool :=
  (match emit x y with | none => r | some z => feed C encode z r, false)

theorem callback_invariant {β γ : Type*} {C width : ℕ} (encode : α → List Bool)
    (hw : ∀ z, (encode z).length = width) (emit : β → γ → Option α)
    (x : β) (y : γ) (r : State α) (hr : Invariant C width encode r) :
    Invariant C width encode (callback C encode emit x y r).1 := by
  cases h : emit x y with
  | none => simpa only [callback, h] using hr
  | some z => simpa only [callback, h] using feed_invariant hr z (hw z)

/-- Array and trie storage are bounded even at incomplete join prefixes. -/
theorem stopped_invariant {β γ σ₁ σ₂ : Type*} {C width : ℕ}
    (read₁ : σ₁ → Option (β × σ₁)) (key₁ : β → ℤ)
    (read₂ : σ₂ → Option (γ × σ₂)) (key₂ : γ → ℤ)
    (encode : α → List Bool) (hw : ∀ z, (encode z).length = width)
    (emit : β → γ → Option α) (B fuel₁ fuel₂ controlFuel : ℕ) (s₁ : σ₁) (s₂ : σ₂) :
    Invariant C width encode (StreamJoin.stopped read₁ key₁ read₂ key₂
      (callback C encode emit) B fuel₁ fuel₂ controlFuel s₁ s₂ empty).state.user := by
  rw [StreamJoin.stopped_eq]
  exact DictionaryPrefixes.run_preserves read₁ key₁ read₂ key₂ (callback C encode emit)
    (Invariant C width encode) (callback_invariant encode hw emit) B fuel₁ fuel₂ controlFuel
    (StreamJoin.start s₁ s₂ empty) (empty_invariant C width encode)

end LowSpaceSubsetSum.RecordedDictionary

end OAI
