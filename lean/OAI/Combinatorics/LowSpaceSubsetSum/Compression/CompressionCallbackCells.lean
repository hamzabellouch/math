import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionCallbacks
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredEncodingCells

namespace OAI

/-! # Live storage of the compression dictionary callbacks

The key is constructed once, the trie inserts only a new path, and the
cached distinct count controls overflow. The lookup callback retains no
new dictionary or list of matches.
-/

namespace LowSpaceSubsetSum.CompressionCallbackCells

variable {n : ℕ}

def weightCode (I : Instance n) (x : ℤ) : (List Bool × ℕ) × ℕ :=
  let mag := StoredEncodingCells.bits x.natAbs (2*inputScale I) 0
  ((decide (x<0)::mag.1.1,mag.1.2+3),mag.2+8)

theorem weightCode_value (I : Instance n) (x : ℤ) :
    (weightCode I x).1 = CompressionCallbacks.weightCode I x := by
  simp only [weightCode,StoredEncodingCells.bits_value,CompressionCallbacks.weightCode,
    CountedWeights.natBits]

theorem weightCode_cells (I : Instance n) (x : ℤ) :
    (weightCode I x).2 ≤ 12*inputScale I+12 := by
  simp only [weightCode,StoredEncodingCells.bits_cells]
  omega

def report (I : Instance n) (C : ℕ) (x y : ℤ) (r : CompressionCallbacks.Dictionary I C) :
    ((CompressionCallbacks.Dictionary I C × Bool) × ℕ) × ℕ :=
  let out := TrieDictionaryCells.safeFeed C (WeightEncoding.weightWidth I)
    (CompressionCallbacks.weightCode I) (weightCode I) (weightCode_value I)
    (CompressionCallbacks.weightCode_width I) (fun _ => 1) (x+y) r
  (((out.1.1,false),out.1.2+6),out.2+16)

theorem report_value (I : Instance n) (C : ℕ) (x y : ℤ)
    (r : CompressionCallbacks.Dictionary I C) :
    (report I C x y r).1 = CompressionCallbacks.report I C x y r := by
  simp only [report,TrieDictionaryCells.safeFeed_value,CompressionCallbacks.report,
    CountedDictionaryCallback.callback]
  apply Prod.ext
  · rfl
  · dsimp only; omega

theorem report_cells (I : Instance n) (C : ℕ) (x y : ℤ)
    (r : CompressionCallbacks.Dictionary I C) :
    (report I C x y r).2 ≤ 26*inputScale I+2*(C+1)+83 := by
  have h := TrieDictionaryCells.safeFeed_cells C (WeightEncoding.weightWidth I)
    (CompressionCallbacks.weightCode I) (weightCode I) (weightCode_value I)
    (CompressionCallbacks.weightCode_width I) (fun _ => 1)
    (12*inputScale I+12) 1 (weightCode_cells I) (fun _ => le_rfl) (x+y) r
  change _+16 ≤ _
  have ha := Nat.add_le_add_right h 16
  exact ha.trans (by unfold WeightEncoding.weightWidth; omega)

def probe (I : Instance n) (tree : BinaryTrie.Tree) (target x y : ℤ) (found : Bool) :
    ((Bool × Bool) × ℕ) × ℕ :=
  let code := weightCode I (target-(x+y))
  let hit := TrieCells.contains tree code.1.1
  (((found || hit.1.1,false),code.1.2+hit.1.2+5),code.2+hit.2+code.1.1.length+16)

theorem probe_value (I : Instance n) (tree : BinaryTrie.Tree) (target x y : ℤ) (found : Bool) :
    (probe I tree target x y found).1 = CompressionCallbacks.probe I tree target x y found := by
  simp only [probe,weightCode_value,TrieCells.contains_value,CompressionCallbacks.probe]

theorem probe_cells (I : Instance n) (tree : BinaryTrie.Tree) (target x y : ℤ) (found : Bool) :
    (probe I tree target x y found).2 ≤ 18*inputScale I+35 := by
  have hcode := weightCode_cells I (target-(x+y))
  have hwidth : (weightCode I (target-(x+y))).1.1.length = WeightEncoding.weightWidth I := by
    rw [weightCode_value,CompressionCallbacks.weightCode_width]
  have hh := TrieCells.contains_cells tree (weightCode I (target-(x+y))).1.1
  rw [hwidth] at hh
  change _+_+_+16 ≤ _
  rw [hwidth]
  unfold WeightEncoding.weightWidth at hh ⊢
  omega

def dictionaryCells {I : Instance n} {C : ℕ} (r : CompressionCallbacks.Dictionary I C) : ℕ :=
  2*r.val.records.size+3*BinaryTrie.nodes r.val.keys.tree+8

theorem dictionaryCells_bound (I : Instance n) (C : ℕ) (r : CompressionCallbacks.Dictionary I C) :
    dictionaryCells r ≤ (6*inputScale I+8)*(C+1)+8 := by
  obtain ⟨hs,ht⟩ := CompressionCallbacks.storage I C r
  unfold dictionaryCells
  nlinarith only [hs,ht]

end LowSpaceSubsetSum.CompressionCallbackCells

end OAI
