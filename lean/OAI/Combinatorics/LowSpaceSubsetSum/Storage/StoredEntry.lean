import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationKeys
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CountedDictionaryCallback

namespace OAI

/-! # Bounded stored representation entries and their executed keys -/

namespace LowSpaceSubsetSum

structure StoredEntry (n : ℕ) where
  value : ℤ
  mask : IndexedMask n

namespace StoredEntry

variable {n : ℕ}

def semantic (x : StoredEntry n) : Entry (Fin n) := ⟨x.value, x.mask.semantic⟩

def encode (I : Instance n) (x : StoredEntry n) : List Bool × ℕ :=
  CountedWeights.entryKey I x.value x.mask.indices

theorem encode_value (I : Instance n) (x : StoredEntry n) :
    (encode I x).1 = WeightEncoding.entryKey I x.semantic :=
  CountedWeights.entryKey_value I x.value x.mask.indices

theorem encode_width (I : Instance n) (x : StoredEntry n) :
    (encode I x).1.length = WeightEncoding.entryWidth I := by
  rw [encode_value, WeightEncoding.entryKey_length]

theorem encode_work (I : Instance n) (x : StoredEntry n) :
    (encode I x).2 ≤ 12 * inputScale I ^ 2 :=
  CountedWeights.entryKey_work I x.value x.mask.indices x.mask.length_le

/-- One scalar and the mask list, including its pointer/header. -/
def cells (x : StoredEntry n) : ℕ := x.mask.indices.length + 2

theorem cells_le (x : StoredEntry n) : x.cells ≤ n + 2 := by
  have h := x.mask.length_le
  exact Nat.add_le_add_right h 2

abbrev Dictionary (I : Instance n) (C : ℕ) :=
  CountedDictionaryCallback.SafeState C (WeightEncoding.entryWidth I) (encode I)

def empty (I : Instance n) (C : ℕ) : Dictionary I C :=
  CountedDictionaryCallback.empty _ _ _

def report {α β : Type*} (I : Instance n) (C : ℕ)
    (emit : α → β → Option (StoredEntry n) × ℕ) :=
  CountedDictionaryCallback.callback C (WeightEncoding.entryWidth I) (encode I)
    (encode_width I) cells emit

theorem report_work {α β : Type*} (I : Instance n) (C E : ℕ)
    (emit : α → β → Option (StoredEntry n) × ℕ) (he : ∀ x y, (emit x y).2 ≤ E)
    (x : α) (y : β) (r : Dictionary I C) :
    (report I C emit x y r).2 ≤ E + 12 * inputScale I ^ 2 + (n + 2) +
      2 * WeightEncoding.entryWidth I + 19 :=
  CountedDictionaryCallback.callback_work C (WeightEncoding.entryWidth I) (encode I)
    (encode_width I) cells emit (12 * inputScale I ^ 2) (n + 2) E
    (encode_work I) cells_le he x y r

/-- Erase bounded-list records while keeping the same trie and array order. -/
def mapDictionary (r : RecordedDictionary.State (StoredEntry n)) :
    RecordedDictionary.State (Entry (Fin n)) :=
  ⟨r.keys, r.records.map semantic⟩

theorem mapDictionary_feed (I : Instance n) (C : ℕ) (x : StoredEntry n)
    (r : RecordedDictionary.State (StoredEntry n)) :
    mapDictionary (RecordedDictionary.feed C (fun x => (encode I x).1) x r) =
      RecordedDictionary.feed C (WeightEncoding.entryKey I) x.semantic (mapDictionary r) := by
  have he : (fun x : StoredEntry n => (encode I x).1) =
      (fun x => WeightEncoding.entryKey I x.semantic) := funext (encode_value I)
  rw [he]
  unfold RecordedDictionary.feed mapDictionary
  dsimp only
  split <;> simp_all only [Array.map_push]

theorem report_value {α β : Type*} (I : Instance n) (C : ℕ)
    (emit : α → β → Option (StoredEntry n) × ℕ)
    (x : α) (y : β) (r : Dictionary I C) :
    (mapDictionary (report I C emit x y r).1.1.val, (report I C emit x y r).1.2) =
      RecordedDictionary.callback C (WeightEncoding.entryKey I)
        (fun x y => (emit x y).1.map semantic) x y (mapDictionary r.val) := by
  cases he : (emit x y).1 with
  | none => simp only [report, CountedDictionaryCallback.callback, he,
      Option.map_none, RecordedDictionary.callback]
  | some z => simp only [report, CountedDictionaryCallback.callback, he,
      Option.map_some, RecordedDictionary.callback,
      CountedDictionaryCallback.feed_value, mapDictionary_feed]

end StoredEntry
end LowSpaceSubsetSum

end OAI
