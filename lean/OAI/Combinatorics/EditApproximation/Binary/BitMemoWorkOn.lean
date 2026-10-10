import OAI.Combinatorics.EditApproximation.Binary.BitRankedMemoOn
import OAI.Combinatorics.EditApproximation.Binary.BitMemoWorkTransfer

namespace OAI

/-! The same exact fresh-key work accounting applies to normalized
programs whose simulation is justified on reachable child values. -/

namespace EditApproximation

theorem rankedBitMemoEvaluate_work_transfer_on {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (expected : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (hprogram : ∀ key, BitQuery.RefinesOn
      (fun child => rankedBitProgramValue rank program child.val)
      (fun word value => word.value = value) (program key) (expected key))
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) (memory : BinaryMemo BinaryFraction)
    (hmemory : bitMemoSound bits encode (rankedBitProgramValue rank program) memory) :
    (rankedBitMemoEvaluate rank program bits encode key memory).localWork =
      rankedMemoKernelWork rank expected bits encode (rankedBitLocalWork rank program)
        key (memory.mapValues BinaryFraction.value) := by
  have hf := congrArg RecursiveMemoResult.freshKeys
    (rankedBitMemoEvaluate_decode_on rank program expected hprogram bits encode hinjective hbounded
      key memory hmemory)
  dsimp only [BitRecursiveMemoResult.decode] at hf
  rw [rankedMemoKernelWork_eq_fresh_sum, ← hf]
  exact rankedBitMemoEvaluate_localWork rank program bits encode hinjective hbounded key memory hmemory

theorem rankedBitProgramValue_value_on {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (expected : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (hprogram : ∀ key, BitQuery.RefinesOn
      (fun child => rankedBitProgramValue rank program child.val)
      (fun word value => word.value = value) (program key) (expected key))
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) :
    (rankedBitProgramValue rank program key).value = rankedProgramValue rank expected key := by
  have hv := congrArg RecursiveMemoResult.value
    (rankedBitMemoEvaluate_decode_on rank program expected hprogram bits encode hinjective hbounded
      key .empty (bitMemoSound_empty _ _ _))
  dsimp only [BitRecursiveMemoResult.decode, BinaryMemo.mapValues] at hv
  rw [(rankedBitMemoEvaluate_sound rank program bits encode hinjective hbounded key .empty
      (bitMemoSound_empty bits encode _)).1] at hv
  exact hv.trans (rankedMemoEvaluate_empty rank expected bits encode hinjective hbounded key)

end EditApproximation

end OAI
