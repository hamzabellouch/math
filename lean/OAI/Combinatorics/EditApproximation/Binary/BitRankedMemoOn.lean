import OAI.Combinatorics.EditApproximation.Binary.BitMemoOn

namespace OAI

/-! Exact rational trace transfer when local output normalization is
proved only on the canonical reachable child words. -/

namespace EditApproximation

theorem rankedBitMemoEvaluate_decode_on {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (expected : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (hprogram : ∀ key, BitQuery.RefinesOn
      (fun child => rankedBitProgramValue rank program child.val)
      (fun word value => word.value = value) (program key) (expected key))
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) (memory : BinaryMemo BinaryFraction)
    (hmemory : bitMemoSound bits encode (rankedBitProgramValue rank program) memory) :
    (rankedBitMemoEvaluate rank program bits encode key memory).decode =
      rankedMemoEvaluate rank expected bits encode key (memory.mapValues BinaryFraction.value) := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      bitMemoSound bits encode (rankedBitProgramValue rank program) memory →
      (rankedBitMemoEvaluate rank program bits encode key memory).decode =
        rankedMemoEvaluate rank expected bits encode key (memory.mapValues BinaryFraction.value) := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory hmem
      rw [rankedBitMemoEvaluate, rankedMemoEvaluate]
      simp only [BinaryMemo.lookupCosted_spec, BinaryMemo.mapValues_lookup]
      cases hfound : memory.lookup (binaryMemoKey bits (encode key)) with
      | some value => simp only [Option.map_some, BitRecursiveMemoResult.decode]
      | none =>
        simp only [Option.map_none]
        have hchildren (child : {child : κ // rank child < rank key}) previous
            (hp : bitMemoSound bits encode (rankedBitProgramValue rank program) previous) :
            (rankedBitMemoEvaluate rank program bits encode child.val previous).value =
                rankedBitProgramValue rank program child.val ∧
            bitMemoSound bits encode (rankedBitProgramValue rank program)
                (rankedBitMemoEvaluate rank program bits encode child.val previous).memory ∧
            (rankedBitMemoEvaluate rank program bits encode child.val previous).decode =
              rankedMemoEvaluate rank expected bits encode child.val
                (previous.mapValues BinaryFraction.value) := by
          have hs := rankedBitMemoEvaluate_sound rank program bits encode hinjective hbounded child.val previous hp
          exact ⟨hs.1, hs.2, ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous hp⟩
        have hr := (BitQuery.runMemo_decode_on
          (fun child : {child : κ // rank child < rank key} => rankedBitProgramValue rank program child.val)
          (bitMemoSound bits encode (rankedBitProgramValue rank program))
          (fun child previous => rankedBitMemoEvaluate rank program bits encode child.val previous)
          (fun child previous => rankedMemoEvaluate rank expected bits encode child.val previous)
          hchildren (hprogram key) memory hmem).1
        have hv := congrArg RecursiveMemoResult.value hr
        have hm := congrArg RecursiveMemoResult.memory hr
        have hf := congrArg RecursiveMemoResult.freshKeys hr
        have hd := congrArg RecursiveMemoResult.dictionaryVisits hr
        have hq := congrArg RecursiveMemoResult.requests hr
        simp only [BitRecursiveMemoResult.decode] at hv hm hf hd hq
        simp only [BinaryMemo.insertCosted_spec, BitRecursiveMemoResult.decode,
          BinaryMemo.mapValues_insert, hv, hm, hf, hd, hq]
  exact hall (rank key) key rfl memory hmemory

end EditApproximation

end OAI
