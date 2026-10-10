import OAI.Combinatorics.EditApproximation.Binary.BitMemoRun
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The rank-decreasing evaluator stores the binary words actually returned
by its local program. Its rational view preserves the fresh-key,
dictionary-visit and request traces. -/

namespace EditApproximation



theorem rankedBitMemoEvaluate_decode {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (expected : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (hprogram : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (program key) (expected key))
    (bits : ℕ) (encode : κ → ℕ) (key : κ) (memory : BinaryMemo BinaryFraction) :
    (rankedBitMemoEvaluate rank program bits encode key memory).decode =
      rankedMemoEvaluate rank expected bits encode key (memory.mapValues BinaryFraction.value) := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      (rankedBitMemoEvaluate rank program bits encode key memory).decode =
        rankedMemoEvaluate rank expected bits encode key (memory.mapValues BinaryFraction.value) := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory
      rw [rankedBitMemoEvaluate, rankedMemoEvaluate]
      simp only [BinaryMemo.lookupCosted_spec, BinaryMemo.mapValues_lookup]
      cases hfound : memory.lookup (binaryMemoKey bits (encode key)) with
      | some value =>
        simp only [Option.map_some, BitRecursiveMemoResult.decode]
      | none =>
        simp only [Option.map_none]
        have hr := BitQuery.runMemo_decode
          (fun (child : {child : κ // rank child < rank key}) previous =>
            rankedBitMemoEvaluate rank program bits encode child.val previous)
          (fun child previous => rankedMemoEvaluate rank expected bits encode child.val previous)
          (fun child previous => ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous)
          (hprogram key) memory
        have hv := congrArg RecursiveMemoResult.value hr
        have hm := congrArg RecursiveMemoResult.memory hr
        have hf := congrArg RecursiveMemoResult.freshKeys hr
        have hd := congrArg RecursiveMemoResult.dictionaryVisits hr
        have hq := congrArg RecursiveMemoResult.requests hr
        simp only [BitRecursiveMemoResult.decode] at hv hm hf hd hq
        simp only [BinaryMemo.insertCosted_spec, BitRecursiveMemoResult.decode,
          BinaryMemo.mapValues_insert, hv, hm, hf, hd, hq]
  exact hall (rank key) key rfl memory

end EditApproximation

end OAI
