import OAI.Combinatorics.EditApproximation.Binary.BitQuerySpace
import OAI.Combinatorics.EditApproximation.Binary.BitRankedMemo
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! A cumulative allocation counter for the actual memo execution. It keeps
all local allocations until the entire run finishes, so it also bounds peak
space. A read retains three continuation/result cells. Each memo call reserves
its address workspace, key bits, traversal frames and the possible new trie
path; existing values and input words are shared by reference. -/

namespace EditApproximation
namespace BitQuery.Heap

def runCells {ι κ : Type*}
    (ask : ι → BinaryMemo BinaryFraction → BitRecursiveMemoResult κ)
    (childCells : ι → BinaryMemo BinaryFraction → ℕ)
    {program : BitQuery ι BinaryFraction} : Heap program → BinaryMemo BinaryFraction → ℕ
  | .done _, _ => 0
  | .read key _ continuation, memory =>
    let first := ask key memory
    3 + childCells key memory + (continuation first.value).runCells ask childCells first.memory
  | .charge cells _ next, memory => cells + next.runCells ask childCells memory

theorem runCells_le {ι κ : Type*}
    (ask : ι → BinaryMemo BinaryFraction → BitRecursiveMemoResult κ)
    (childCells : ι → BinaryMemo BinaryFraction → ℕ) (D : ℕ)
    (hchild : ∀ key memory, childCells key memory + 3 ≤
      3 * (ask key memory).localWork + D * (ask key memory).requests)
    {program : BitQuery ι BinaryFraction} (heap : Heap program)
    (memory : BinaryMemo BinaryFraction) :
    heap.runCells ask childCells memory ≤
      3 * (BitQuery.runMemo ask program memory).localWork +
        D * (BitQuery.runMemo ask program memory).requests := by
  induction heap generalizing memory with
  | done value => simp only [runCells, BitQuery.runMemo, Nat.mul_zero, Nat.add_zero, le_refl]
  | charge cells bound next ih =>
    have h := ih memory
    simp only [runCells, BitQuery.runMemo]
    omega
  | read key next continuation ih =>
    have hc := hchild key memory
    have hr := ih (ask key memory).value (ask key memory).memory
    simp only [runCells, BitQuery.runMemo, Nat.mul_add]
    omega

end BitQuery.Heap

/-- Sixteen scalar/frame slots suffice in addition to eight slots per key
bit and the supplied address-construction workspace; the larger fixed reserve
also covers the result record and the empty-trie case. -/


def rankedBitMemoCells {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (heap : ∀ key, BitQuery.Heap (program key))
    (bits : ℕ) (encode addressCells : κ → ℕ) (key : κ) (memory : BinaryMemo BinaryFraction) : ℕ :=
  let found := memory.lookupCosted (binaryMemoKey bits (encode key))
  match found.1 with
  | some _ => memoRequestCells bits (addressCells key)
  | none => memoRequestCells bits (addressCells key) + (heap key).runCells
      (fun child previous => rankedBitMemoEvaluate rank program bits encode child.val previous)
      (fun child previous => rankedBitMemoCells rank program heap bits encode addressCells child.val previous)
      memory
termination_by rank key
decreasing_by exact child.property

theorem rankedBitMemoCells_le {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (heap : ∀ key, BitQuery.Heap (program key))
    (bits : ℕ) (encode addressCells : κ → ℕ) (A : ℕ)
    (haddress : ∀ key, addressCells key ≤ A) (key : κ) (memory : BinaryMemo BinaryFraction) :
    rankedBitMemoCells rank program heap bits encode addressCells key memory + 3 ≤
      3 * (rankedBitMemoEvaluate rank program bits encode key memory).localWork +
        (memoRequestCells bits A + 3) * (rankedBitMemoEvaluate rank program bits encode key memory).requests := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      rankedBitMemoCells rank program heap bits encode addressCells key memory + 3 ≤
        3 * (rankedBitMemoEvaluate rank program bits encode key memory).localWork +
          (memoRequestCells bits A + 3) * (rankedBitMemoEvaluate rank program bits encode key memory).requests := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory
      have ha : memoRequestCells bits (addressCells key) ≤ memoRequestCells bits A := by
        unfold memoRequestCells
        exact Nat.add_le_add_right (Nat.add_le_add_right (haddress key) _) _
      rw [rankedBitMemoCells, rankedBitMemoEvaluate]
      dsimp only
      cases hf : (memory.lookupCosted (binaryMemoKey bits (encode key))).1 with
      | some value =>
        simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add]
        omega
      | none =>
        have hc (child : {child : κ // rank child < rank key}) previous :=
          ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous
        have hr := BitQuery.Heap.runCells_le
          (fun child previous => rankedBitMemoEvaluate rank program bits encode child.val previous)
          (fun child previous => rankedBitMemoCells rank program heap bits encode addressCells child.val previous)
          (memoRequestCells bits A + 3) hc (heap key) memory
        simp only [Nat.mul_add, Nat.mul_one]
        omega
  exact hall (rank key) key rfl memory

end EditApproximation

end OAI
