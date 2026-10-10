import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CountedDictionaryCallback
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedWeights
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.StreamWitness

namespace OAI

/-! # Executed fixed-width callbacks for the compression join

The left dictionary keeps its distinct-key count in the safe state. It never
traverses the trie to count entries during insertion. The right callback
computes one fixed-width key and one trie lookup.
-/

namespace LowSpaceSubsetSum.CompressionCallbacks

variable {n : ℕ}

def weightCode (I : Instance n) (x : ℤ) : List Bool × ℕ :=
  let m := CountedWeights.natBits (2 * inputScale I) x.natAbs
  (decide (x < 0) :: m.1, m.2 + 3)

theorem weightCode_value (I : Instance n) (x : ℤ) :
    (weightCode I x).1 = WeightEncoding.weightKey I x := by
  simp only [weightCode, CountedWeights.natBits_value,
    WeightEncoding.weightKey, WeightEncoding.signedBits]

theorem weightCode_width (I : Instance n) (x : ℤ) :
    (weightCode I x).1.length = WeightEncoding.weightWidth I := by
  rw [weightCode_value, WeightEncoding.weightKey_length]

theorem weightCode_work (I : Instance n) (x : ℤ) :
    (weightCode I x).2 = 6 * inputScale I + 4 := by
  simp only [weightCode, CountedWeights.natBits, CountedWeights.bits_work]
  omega

abbrev Dictionary (I : Instance n) (C : ℕ) :=
  CountedDictionaryCallback.SafeState C (WeightEncoding.weightWidth I) (weightCode I)

def empty (I : Instance n) (C : ℕ) : Dictionary I C :=
  CountedDictionaryCallback.empty _ _ _

def report (I : Instance n) (C : ℕ) (x y : ℤ) (state : Dictionary I C) :
    (Dictionary I C × Bool) × ℕ :=
  CountedDictionaryCallback.callback C (WeightEncoding.weightWidth I) (weightCode I)
    (weightCode_width I) (fun _ => 1) (fun a b => (some (a + b), 1)) x y state

theorem report_value (I : Instance n) (C : ℕ) (x y : ℤ) (state : Dictionary I C) :
    ((report I C x y state).1.1.val.keys, (report I C x y state).1.2) =
      BinaryTrie.callback C (fun a b => WeightEncoding.weightKey I (a + b)) x y state.val.keys := by
  change ((CountedDictionaryCallback.feed C (WeightEncoding.weightWidth I) (weightCode I)
    (weightCode_width I) (fun _ => 1) (x + y) state).1.val.keys, false) = _
  rw [CountedDictionaryCallback.feed_value]
  simp only [RecordedDictionary.feed_keys, weightCode_value, BinaryTrie.callback]

theorem report_work (I : Instance n) (C : ℕ) (x y : ℤ) (state : Dictionary I C) :
    (report I C x y state).2 ≤ 10 * inputScale I + 27 := by
  have h := CountedDictionaryCallback.callback_work C (WeightEncoding.weightWidth I)
    (weightCode I) (weightCode_width I) (fun _ => 1) (fun a b : ℤ => (some (a + b), 1))
    (6 * inputScale I + 4) 1 1 (fun a => (weightCode_work I a).le)
    (fun _ => le_rfl) (fun _ _ => le_rfl) x y state
  change (report I C x y state).2 ≤ _ at h
  unfold WeightEncoding.weightWidth at h
  omega

def probe (I : Instance n) (tree : BinaryTrie.Tree) (target x y : ℤ) (found : Bool) :
    (Bool × Bool) × ℕ :=
  let k := weightCode I (target - (x + y))
  let hit := CountedTrie.contains tree k.1
  ((found || hit.1, false), k.2 + hit.2 + 5)

theorem probe_value (I : Instance n) (tree : BinaryTrie.Tree) (target x y : ℤ) (found : Bool) :
    (probe I tree target x y found).1 =
      StreamWitness.remember
        (fun x y => BinaryTrie.contains tree (WeightEncoding.weightKey I (target - (x + y))))
        x y found := by
  simp only [probe, CountedTrie.contains_value, weightCode_value, StreamWitness.remember]

theorem probe_work (I : Instance n) (tree : BinaryTrie.Tree) (target x y : ℤ) (found : Bool) :
    (probe I tree target x y found).2 ≤ 8 * inputScale I + 11 := by
  have h := CountedTrie.contains_work tree (weightCode I (target - (x + y))).1
  rw [weightCode_width] at h
  change (weightCode I (target - (x + y))).2 + _ + 5 ≤ _
  rw [weightCode_work]
  unfold WeightEncoding.weightWidth at h
  omega

theorem report_scale (I : Instance n) (hn : 10000 ≤ n) (C : ℕ)
    (x y : ℤ) (state : Dictionary I C) :
    (report I C x y state).2 ≤ inputScale I ^ 2 := by
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  exact (report_work I C x y state).trans (by nlinarith only [hu])

theorem probe_scale (I : Instance n) (hn : 10000 ≤ n)
    (tree : BinaryTrie.Tree) (target x y : ℤ) (found : Bool) :
    (probe I tree target x y found).2 ≤ inputScale I ^ 2 := by
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  exact (probe_work I tree target x y found).trans (by nlinarith only [hu])

theorem storage (I : Instance n) (C : ℕ) (state : Dictionary I C) :
    state.val.records.size ≤ C + 1 ∧
      BinaryTrie.nodes state.val.keys.tree ≤ (2 * inputScale I + 2) * (C + 1) := by
  simpa only [WeightEncoding.weightWidth, Nat.add_assoc] using
    RecordedDictionary.storage state.property

end LowSpaceSubsetSum.CompressionCallbacks

end OAI
