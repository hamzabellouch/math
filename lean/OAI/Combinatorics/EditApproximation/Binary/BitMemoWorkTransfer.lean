import OAI.Combinatorics.EditApproximation.Binary.BitMemoWork
import OAI.Combinatorics.EditApproximation.Geometry.RankedMemoKernelFresh

namespace OAI

/-! Transfer the concrete binary evaluator's measured local work to the
already bounded rational trace, using equality of the actual miss list. -/

namespace EditApproximation

theorem rankedBitMemoEvaluate_work_transfer {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (expected : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (hprogram : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (program key) (expected key))
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) (memory : BinaryMemo BinaryFraction)
    (hmemory : bitMemoSound bits encode (rankedBitProgramValue rank program) memory) :
    (rankedBitMemoEvaluate rank program bits encode key memory).localWork =
      rankedMemoKernelWork rank expected bits encode (rankedBitLocalWork rank program)
        key (memory.mapValues BinaryFraction.value) := by
  have hf := congrArg RecursiveMemoResult.freshKeys
    (rankedBitMemoEvaluate_decode rank program expected hprogram bits encode key memory)
  dsimp only [BitRecursiveMemoResult.decode] at hf
  rw [rankedMemoKernelWork_eq_fresh_sum, ← hf]
  exact rankedBitMemoEvaluate_localWork rank program bits encode hinjective hbounded key memory hmemory

theorem rankedBitProgramValue_value {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (expected : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (hprogram : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (program key) (expected key))
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) :
    (rankedBitProgramValue rank program key).value = rankedProgramValue rank expected key := by
  have hv := congrArg RecursiveMemoResult.value
    (rankedBitMemoEvaluate_decode rank program expected hprogram bits encode key .empty)
  dsimp only [BitRecursiveMemoResult.decode, BinaryMemo.mapValues] at hv
  rw [(rankedBitMemoEvaluate_sound rank program bits encode hinjective hbounded key .empty
      (bitMemoSound_empty bits encode _)).1] at hv
  exact hv.trans (rankedMemoEvaluate_empty rank expected bits encode hinjective hbounded key)

end EditApproximation

end OAI
