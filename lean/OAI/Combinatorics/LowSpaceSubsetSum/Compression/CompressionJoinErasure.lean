import OAI.Combinatorics.LowSpaceSubsetSum.Compression.BudgetedCompressionJoin
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionQueryBounds

namespace OAI

/-! # Compression dictionary erasure through the full stopped join

The bounded dictionary carries its invariant and distinct-key count in the
execution state. Erasure preserves all join cursors and counters, including
prefixes which overflow the dictionary.
-/

namespace LowSpaceSubsetSum.CompressionData

variable {n : ℕ} (D : CompressionData n)

def leftReference (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (z : Fin q.val) (fuel : ℕ) :=
  BudgetedCompressionJoin.reference q.val z.val B
    (D.storedRightArray e q 0) (D.storedRightArray e q 1)
    (CompressionCallbacks.report D.input (compressionDictionaryCapacity n))
    (D.streamLength e 0) (D.streamLength e 1) fuel
    (D.groupStart e q 0 .direct) (D.groupStart e q 1 (.complementary z.val))
    (CompressionCallbacks.empty D.input (compressionDictionaryCapacity n))

def rightReference (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (z : Fin q.val) (tree : BinaryTrie.Tree) (fuel : ℕ) :=
  let target := (D.input.target : ℤ) - z.val
  BudgetedCompressionJoin.reference q.val target B
    (D.storedRightArray e q 2) (D.storedRightArray e q 3)
    (CompressionCallbacks.probe D.input tree D.input.target)
    (D.streamLength e 2) (D.streamLength e 3) fuel
    (D.groupStart e q 2 .direct) (D.groupStart e q 3 (.complementary target)) false

def eraseCompression (a : CompressionCallbacks.Dictionary D.input (compressionDictionaryCapacity n)) :=
  a.val.keys

theorem leftReference_value (B : ℕ) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (z : Fin q.val) (fuel : ℕ) :
    StreamJoin.mapUser D.eraseCompression (D.leftReference B e q z fuel).1.state =
      D.leftJoin B e q z fuel := by
  let report := fun x y a =>
    (CompressionCallbacks.report D.input (compressionDictionaryCapacity n) x y a).1
  let report' := BinaryTrie.callback (compressionDictionaryCapacity n)
    (fun x y => WeightEncoding.weightKey D.input (x + y))
  have hf : ∀ x y a, report' x y (D.eraseCompression a) =
      (D.eraseCompression (report x y a).1, (report x y a).2) := by
    intro x y a
    exact (CompressionCallbacks.report_value D.input (compressionDictionaryCapacity n) x y a).symm
  have h₀ : (fun s => (CompressionReader.read q.val .direct (D.storedRightArray e q 0) s).1) =
      D.groupRead e q 0 .direct := funext (CompressionReader.groupRead_value D e q 0 .direct)
  have h₁ : (fun s => (CompressionReader.read q.val (.complementary z.val)
      (D.storedRightArray e q 1) s).1) = D.groupRead e q 1 (.complementary z.val) :=
    funext (CompressionReader.groupRead_value D e q 1 (.complementary z.val))
  unfold leftReference
  rw [BudgetedCompressionJoin.reference_value, StreamJoin.stopped_eq]
  change StreamJoin.mapUser D.eraseCompression (StreamJoin.run _ _ _ _ report _ _ _ _ _ _ _) = _
  rw [StreamJoin.run_mapUser _ _ _ _ report report' D.eraseCompression hf, h₀, h₁]
  rfl

theorem rightReference_value (B : ℕ) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (z : Fin q.val) (tree : BinaryTrie.Tree) (fuel : ℕ) :
    (D.rightReference B e q z tree fuel).1.state = D.rightJoin B e q z tree fuel := by
  let target := (D.input.target : ℤ) - z.val
  have h₂ : (fun s => (CompressionReader.read q.val .direct (D.storedRightArray e q 2) s).1) =
      D.groupRead e q 2 .direct := funext (CompressionReader.groupRead_value D e q 2 .direct)
  have h₃ : (fun s => (CompressionReader.read q.val (.complementary target)
      (D.storedRightArray e q 3) s).1) = D.groupRead e q 3 (.complementary target) :=
    funext (CompressionReader.groupRead_value D e q 3 (.complementary target))
  have hr : (fun x y a => (CompressionCallbacks.probe D.input tree D.input.target x y a).1) =
      StreamWitness.remember (fun x y => BinaryTrie.contains tree
        (WeightEncoding.weightKey D.input ((D.input.target : ℤ) - (x + y)))) := by
    funext x y a
    exact CompressionCallbacks.probe_value _ _ _ _ _ _
  unfold rightReference
  dsimp only
  rw [BudgetedCompressionJoin.reference_value, StreamJoin.stopped_eq, h₂, h₃, hr]
  rfl

end LowSpaceSubsetSum.CompressionData

end OAI
