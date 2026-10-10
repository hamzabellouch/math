import OAI.Combinatorics.LowSpaceSubsetSum.Compression.BudgetedCompressionPass
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionJoinErasure
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionTrialLedger
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationTaskSpace

namespace OAI

/-! # The compression residue pass and its original source ledger

The contexts in `passData` specify the shared-array initializer values.
The allowance bounds the two joins, with context construction charged
separately.
-/

namespace LowSpaceSubsetSum.CompressionData

variable {n : ℕ} (D : CompressionData n)

def passData (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n) (z : Fin q.val) :
    BudgetedCompressionPass.Data q.val D.input.target z.val :=
  ⟨⟨D.storedRightArray e q 0, _, D.groupStart e q 0 .direct⟩,
    ⟨D.storedRightArray e q 1, _, D.groupStart e q 1 (.complementary z.val)⟩,
    ⟨D.storedRightArray e q 2, _, D.groupStart e q 2 .direct⟩,
    ⟨D.storedRightArray e q 3, _, D.groupStart e q 3 (.complementary ((D.input.target : ℤ) - z.val))⟩,
    D.streamLength e 0, D.streamLength e 1, D.streamLength e 2, D.streamLength e 3⟩

theorem pass_left_value (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (z : Fin q.val) :
    StreamJoin.mapUser D.eraseCompression
      (BudgetedCompressionPass.leftFull D.input (compressionDictionaryCapacity n) B
        (D.passData e q z)).1.state =
      D.leftJoin B e q z (D.streamLength e 0 + D.streamLength e 1 + 1) :=
  D.leftReference_value B e q z _

theorem pass_right_value (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (z : Fin q.val) (tree : BinaryTrie.Tree) :
    (BudgetedCompressionPass.rightFull D.input B (D.passData e q z) tree).1.state =
      D.rightJoin B e q z tree (D.streamLength e 2 + D.streamLength e 3 + 1) :=
  D.rightReference_value B e q z tree _

theorem pass_reference (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (z : Fin q.val) (he : D.compactTests e = true) :
    BudgetedCompressionPass.reference D.input (compressionDictionaryCapacity n) B (D.passData e q z) =
      D.residuePass B e q z := by
  have hl := congrArg StreamJoin.State.user (D.pass_left_value B e q z)
  change (BudgetedCompressionPass.leftFull D.input (compressionDictionaryCapacity n) B
    (D.passData e q z)).1.state.user.val.keys = D.actualLeftDictionary B e q z at hl
  dsimp only [BudgetedCompressionPass.reference, residuePass]
  rw [hl, he, ite_eq_left rfl]
  split
  · rfl
  · exact congrArg StreamJoin.State.user (D.pass_right_value B e q z _)

theorem pass_leftKeys (B : ℕ) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (z : Fin q.val) :
    (BudgetedCompressionPass.leftFull D.input (compressionDictionaryCapacity n) B
      (D.passData e q z)).1.state.user.val.keys =
      (D.leftJoin B e q z (D.streamLength e 0 + D.streamLength e 1 + 1)).user :=
  congrArg StreamJoin.State.user (D.pass_left_value B e q z)

theorem pass_leftBill (B : ℕ) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (z : Fin q.val) :
    BudgetedCompressionPass.leftBill D.input (compressionDictionaryCapacity n) B
      (D.passData e q z) = inputScale D.input ^ 5 *
        (D.leftJoin B e q z (D.streamLength e 0 + D.streamLength e 1 + 1)).queries +
        B * (D.leftJoin B e q z (D.streamLength e 0 + D.streamLength e 1 + 1)).copies + 4 := by
  have hq := congrArg StreamJoin.State.queries (D.pass_left_value B e q z)
  have hc := congrArg StreamJoin.State.copies (D.pass_left_value B e q z)
  dsimp only [StreamJoin.mapUser] at hq hc
  dsimp only [BudgetedCompressionPass.leftBill]
  rw [hq, hc]

theorem pass_rightBill (B : ℕ) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (z : Fin q.val) (tree : BinaryTrie.Tree) :
    BudgetedCompressionPass.rightBill D.input B (D.passData e q z) tree =
      inputScale D.input ^ 5 *
        (D.rightJoin B e q z tree (D.streamLength e 2 + D.streamLength e 3 + 1)).queries +
        B * (D.rightJoin B e q z tree (D.streamLength e 2 + D.streamLength e 3 + 1)).copies + 4 := by
  have hq := congrArg StreamJoin.State.queries (D.pass_right_value B e q z tree)
  have hc := congrArg StreamJoin.State.copies (D.pass_right_value B e q z tree)
  dsimp only [BudgetedCompressionPass.rightBill]
  rw [hq, hc]

theorem pass_allowance (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (z : Fin q.val) (he : D.compactTests e = true) :
    BudgetedCompressionPass.allowance D.input (compressionDictionaryCapacity n) B (D.passData e q z) ≤
      inputScale D.input ^ 5 * (D.residueLedger B e q z).queries +
        B * (D.residueLedger B e q z).copies + 16 := by
  dsimp only [BudgetedCompressionPass.allowance]
  rw [D.pass_leftKeys, D.pass_leftBill]
  simp only [residueLedger, he, ↓reduceIte]
  split
  · dsimp only
    omega
  · rw [D.pass_rightBill]
    simp only [Nat.mul_add]
    omega

theorem pass_depth (e : Equiv.Perm (Fin n)) (he : D.compactTests e = true)
    (hn : 10000 ≤ n) (i : Fin 4) : Nat.clog 2 (D.storedFirst e i).toArray.size ≤ n := by
  apply Nat.clog_le_of_le_pow
  simp only [List.size_toArray]
  apply (D.storedFirst_length_bound e he i).trans
  apply Nat.pow_le_pow_right (by decide)
  have hr := compression_cap_rate (by omega : 40 ≤ n)
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hh : (compressionCapExponent n : ℝ) ≤ n := by linarith
  exact_mod_cast hh

theorem pass_account (e : Equiv.Perm (Fin n)) (he : D.compactTests e = true)
    (q : CompressionSetup.PrimeSpace n) (z : Fin q.val) (budget : ℕ) (hn : 10000 ≤ n) :
    BudgetedSeparatorFlow.Account budget
      (BudgetedCompressionPass.run D.input (compressionDictionaryCapacity n)
        (representationBufferCapacity n) (D.passData e q z) budget) := by
  have copy (i : Fin 4) (mode : FilteredStream.Mode) :
      10 * 2 ^ (Nat.clog 2 (D.storedFirst e i).toArray.size + 1) ≤ representationBufferCapacity n := by
    have h := D.snapshotCells_le_buffer e he (by omega) q i mode (D.groupStart e q i mode)
    have ht := Tournament.nodes_exact (D.groupStart e q i mode).tree
    have hp : 0 < 2 ^ (Nat.clog 2 (D.storedFirst e i).toArray.size + 1) := by positivity
    unfold snapshotCells representationBufferCapacity at *
    omega
  exact BudgetedCompressionPass.account _ _ _ _ _ hn
    (D.pass_depth e he hn 0) (D.pass_depth e he hn 1)
    (D.pass_depth e he hn 2) (D.pass_depth e he hn 3)
    (copy 1 (.complementary z.val))
    (copy 3 (.complementary ((D.input.target : ℤ) - z.val)))

end LowSpaceSubsetSum.CompressionData

end OAI
