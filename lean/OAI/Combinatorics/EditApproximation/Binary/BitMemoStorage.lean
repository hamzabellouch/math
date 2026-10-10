import OAI.Combinatorics.EditApproximation.Binary.BitMemoSound
import OAI.Combinatorics.EditApproximation.Geometry.RankedMemoStorage
import OAI.Combinatorics.EditApproximation.Binary.BinaryMemoSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Storage of the actual binary-word memo. Node paths are identical to
the rational evaluator, while stored numerator/denominator bits are
bounded using the deterministic returned-word invariant. -/

namespace EditApproximation
namespace BinaryMemo



theorem fractionStorage_le (memory : BinaryMemo BinaryFraction) (B : ℕ)
    (hmem : AllValues (fun word => word.width ≤ B) memory) :
    memory.fractionStorage ≤ (2 * B + 4) * memory.nodes := by
  induction memory with
  | empty => simp only [fractionStorage, nodes, Nat.mul_zero, le_refl]
  | node word left right ihl ihr =>
    have hl : AllValues (fun word => word.width ≤ B) left := by
      intro key value h
      exact hmem (false :: key) value h
    have hr : AllValues (fun word => word.width ≤ B) right := by
      intro key value h
      exact hmem (true :: key) value h
    have hw : (word.map fun w => w.numerator.bits.length + w.denominator.length + 1).getD 0 ≤ 2 * B + 1 := by
      cases word with
      | none => exact Nat.zero_le _
      | some word =>
        have h := hmem [] word rfl
        have hn := (le_max_left word.numerator.bits.length word.denominator.length).trans h
        have hd := (le_max_right word.numerator.bits.length word.denominator.length).trans h
        change _ + _ + 1 ≤ _
        omega
    have hleft := ihl hl
    have hright := ihr hr
    simp only [fractionStorage, nodes]
    nlinarith only [hw, hleft, hright]

end BinaryMemo

theorem rankedBitMemoEvaluate_widths {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (B : ℕ)
    (hwidth : ∀ key, (rankedBitProgramValue rank program key).width ≤ B)
    (key : κ) (memory : BinaryMemo BinaryFraction)
    (hsound : bitMemoSound bits encode (rankedBitProgramValue rank program) memory)
    (hmem : BinaryMemo.AllValues (fun word => word.width ≤ B) memory) :
    BinaryMemo.AllValues (fun word => word.width ≤ B)
      (rankedBitMemoEvaluate rank program bits encode key memory).memory := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      bitMemoSound bits encode (rankedBitProgramValue rank program) memory →
      BinaryMemo.AllValues (fun word => word.width ≤ B) memory →
      BinaryMemo.AllValues (fun word => word.width ≤ B)
        (rankedBitMemoEvaluate rank program bits encode key memory).memory := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory hs hm
      rw [rankedBitMemoEvaluate]
      simp only [BinaryMemo.lookupCosted_spec]
      split
      · exact hm
      · have hchildren : ∀ (child : {child : κ // rank child < rank key}) previous,
            bitMemoSound bits encode (rankedBitProgramValue rank program) previous ∧
              BinaryMemo.AllValues (fun word => word.width ≤ B) previous →
            (rankedBitMemoEvaluate rank program bits encode child.val previous).value =
                rankedBitProgramValue rank program child.val ∧
              (bitMemoSound bits encode (rankedBitProgramValue rank program)
                  (rankedBitMemoEvaluate rank program bits encode child.val previous).memory ∧
                BinaryMemo.AllValues (fun word => word.width ≤ B)
                  (rankedBitMemoEvaluate rank program bits encode child.val previous).memory) := by
          intro child previous hp
          have hv := rankedBitMemoEvaluate_sound rank program bits encode hinjective hbounded child.val previous hp.1
          exact ⟨hv.1, hv.2, ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous hp.1 hp.2⟩
        have hr := BitQuery.runMemo_sound
          (fun child : {child : κ // rank child < rank key} => rankedBitProgramValue rank program child.val)
          (fun previous => bitMemoSound bits encode (rankedBitProgramValue rank program) previous ∧
            BinaryMemo.AllValues (fun word => word.width ≤ B) previous)
          (fun child previous => rankedBitMemoEvaluate rank program bits encode child.val previous)
          hchildren (program key) memory ⟨hs, hm⟩
        have hv : (BitQuery.runMemo
            (fun child previous => rankedBitMemoEvaluate rank program bits encode child.val previous)
            (program key) memory).value = rankedBitProgramValue rank program key := by
          rw [rankedBitProgramValue]
          exact hr.1
        simp only [BinaryMemo.insertCosted_spec]
        exact hr.2.2.insert _ _ (hv.symm ▸ hwidth key)
  exact hall (rank key) key rfl memory hsound hmem

theorem rankedBitMemoEvaluate_nodes_bound {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (expected : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (hprogram : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (program key) (expected key)) (bits : ℕ) (encode : κ → ℕ) (key : κ) :
    (rankedBitMemoEvaluate rank program bits encode key .empty).memory.nodes + 1 ≤ 2 ^ (bits + 1) := by
  have h := congrArg (fun result : RecursiveMemoResult κ => result.memory.nodes)
    (rankedBitMemoEvaluate_decode rank program expected hprogram bits encode key .empty)
  simp only [BitRecursiveMemoResult.decode, BinaryMemo.mapValues_nodes, BinaryMemo.mapValues] at h
  rw [h]
  exact rankedMemoEvaluate_nodes_bound rank expected bits encode key

end EditApproximation

end OAI
