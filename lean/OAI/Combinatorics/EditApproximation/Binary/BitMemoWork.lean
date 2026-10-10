import OAI.Combinatorics.EditApproximation.Binary.BitMemoSound
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The binary memo's local-work counter is exactly the intrinsic Boolean
work summed over actual cache misses. Recursive calls and cache hits do
not trigger a second charge for a previously computed local body. -/

namespace EditApproximation
namespace BitQuery

theorem runMemo_work_eq {ι κ : Type*} (answer : ι → BinaryFraction)
    (invariant : BinaryMemo BinaryFraction → Prop)
    (ask : ι → BinaryMemo BinaryFraction → BitRecursiveMemoResult κ) (weight : κ → ℕ)
    (hsound : ∀ key memory, invariant memory →
      (ask key memory).value = answer key ∧ invariant (ask key memory).memory)
    (hwork : ∀ key memory, invariant memory →
      (ask key memory).localWork = ((ask key memory).freshKeys.map weight).sum)
    (program : BitQuery ι BinaryFraction) (memory : BinaryMemo BinaryFraction)
    (hmemory : invariant memory) :
    (runMemo ask program memory).localWork = program.work answer (fun _ => 0) +
      ((runMemo ask program memory).freshKeys.map weight).sum := by
  induction program generalizing memory with
  | done result => rfl
  | charge steps next ih =>
    simp only [runMemo, work]
    rw [ih memory hmemory]
    omega
  | read key next ih =>
    have hf := hsound key memory hmemory
    have hw := hwork key memory hmemory
    have hr := ih (ask key memory).value (ask key memory).memory hf.2
    simp only [runMemo, work, List.map_append, List.sum_append, Nat.zero_add]
    rw [hw, hr, hf.1]
    omega

end BitQuery



theorem rankedBitMemoEvaluate_localWork {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) (memory : BinaryMemo BinaryFraction)
    (hmemory : bitMemoSound bits encode (rankedBitProgramValue rank program) memory) :
    (rankedBitMemoEvaluate rank program bits encode key memory).localWork =
      ((rankedBitMemoEvaluate rank program bits encode key memory).freshKeys.map
        (rankedBitLocalWork rank program)).sum := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      bitMemoSound bits encode (rankedBitProgramValue rank program) memory →
      (rankedBitMemoEvaluate rank program bits encode key memory).localWork =
        ((rankedBitMemoEvaluate rank program bits encode key memory).freshKeys.map
          (rankedBitLocalWork rank program)).sum := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory hmem
      rw [rankedBitMemoEvaluate]
      split
      · rfl
      · have hs : ∀ (child : {child : κ // rank child < rank key}) previous,
            bitMemoSound bits encode (rankedBitProgramValue rank program) previous →
            (rankedBitMemoEvaluate rank program bits encode child.val previous).value =
                rankedBitProgramValue rank program child.val ∧
              bitMemoSound bits encode (rankedBitProgramValue rank program)
                (rankedBitMemoEvaluate rank program bits encode child.val previous).memory := by
          intro child previous hp
          exact rankedBitMemoEvaluate_sound rank program bits encode hinjective hbounded child.val previous hp
        have hw : ∀ (child : {child : κ // rank child < rank key}) previous,
            bitMemoSound bits encode (rankedBitProgramValue rank program) previous →
            (rankedBitMemoEvaluate rank program bits encode child.val previous).localWork =
              ((rankedBitMemoEvaluate rank program bits encode child.val previous).freshKeys.map
                (rankedBitLocalWork rank program)).sum := by
          intro child previous hp
          exact ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous hp
        have hr := BitQuery.runMemo_work_eq
          (fun child : {child : κ // rank child < rank key} => rankedBitProgramValue rank program child.val)
          (bitMemoSound bits encode (rankedBitProgramValue rank program))
          (fun child previous => rankedBitMemoEvaluate rank program bits encode child.val previous)
          (rankedBitLocalWork rank program) hs hw (program key) memory hmem
        simpa only [List.map_cons, List.sum_cons, rankedBitLocalWork] using hr
  exact hall (rank key) key rfl memory hmemory

end EditApproximation

end OAI
