import OAI.Combinatorics.EditApproximation.Binary.BitRankedMemo
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Memo hits return the same concrete binary word as the deterministic
rank-decreasing program. This stronger invariant also fixes the local
arithmetic work on repeated reads, independently of cache history. -/

namespace EditApproximation

def bitMemoSound {κ : Type*} (bits : ℕ) (encode : κ → ℕ)
    (expected : κ → BinaryFraction) (memory : BinaryMemo BinaryFraction) : Prop :=
  ∀ key value, memory.lookup (binaryMemoKey bits (encode key)) = some value → value = expected key


theorem bitMemoSound_empty {κ : Type*} (bits : ℕ) (encode : κ → ℕ)
    (expected : κ → BinaryFraction) : bitMemoSound bits encode expected .empty := by
  intro key value hvalue
  rw [BinaryMemo.lookup_empty] at hvalue
  cases hvalue

namespace BitQuery

theorem runMemo_sound {ι κ : Type*} (answer : ι → BinaryFraction)
    (invariant : BinaryMemo BinaryFraction → Prop)
    (ask : ι → BinaryMemo BinaryFraction → BitRecursiveMemoResult κ)
    (hask : ∀ key memory, invariant memory →
      (ask key memory).value = answer key ∧ invariant (ask key memory).memory)
    (program : BitQuery ι BinaryFraction) (memory : BinaryMemo BinaryFraction)
    (hmemory : invariant memory) :
    (runMemo ask program memory).value = program.value answer ∧
      invariant (runMemo ask program memory).memory := by
  induction program generalizing memory with
  | done result => exact ⟨rfl, hmemory⟩
  | charge steps next ih => exact ih memory hmemory
  | read key next ih =>
    have hf := hask key memory hmemory
    have hr := ih (ask key memory).value (ask key memory).memory hf.2
    exact ⟨by simpa only [runMemo, value, hf.1] using hr.1, hr.2⟩

end BitQuery



theorem bitMemoSound_insert {κ : Type*} (bits : ℕ) (encode : κ → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (expected : κ → BinaryFraction) (memory : BinaryMemo BinaryFraction)
    (hmemory : bitMemoSound bits encode expected memory) (key : κ) :
    bitMemoSound bits encode expected
      (memory.insert (binaryMemoKey bits (encode key)) (expected key)) := by
  intro other value hvalue
  rw [binaryMemo_lookup_insert _ bits (encode key) (encode other) (hbounded key) (hbounded other)] at hvalue
  split_ifs at hvalue with heq
  · have hk := hinjective heq
    subst other
    exact Option.some.inj hvalue.symm
  · exact hmemory other value hvalue

theorem rankedBitMemoEvaluate_sound {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) (memory : BinaryMemo BinaryFraction)
    (hmemory : bitMemoSound bits encode (rankedBitProgramValue rank program) memory) :
    (rankedBitMemoEvaluate rank program bits encode key memory).value = rankedBitProgramValue rank program key ∧
      bitMemoSound bits encode (rankedBitProgramValue rank program)
        (rankedBitMemoEvaluate rank program bits encode key memory).memory := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      bitMemoSound bits encode (rankedBitProgramValue rank program) memory →
      (rankedBitMemoEvaluate rank program bits encode key memory).value = rankedBitProgramValue rank program key ∧
        bitMemoSound bits encode (rankedBitProgramValue rank program)
          (rankedBitMemoEvaluate rank program bits encode key memory).memory := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory hmem
      rw [rankedBitMemoEvaluate]
      simp only [BinaryMemo.lookupCosted_spec]
      split
      · rename_i result hresult
        exact ⟨hmem key result hresult, hmem⟩
      · have hchildren : ∀ (child : {child : κ // rank child < rank key}) previous,
            bitMemoSound bits encode (rankedBitProgramValue rank program) previous →
            (rankedBitMemoEvaluate rank program bits encode child.val previous).value =
                rankedBitProgramValue rank program child.val ∧
              bitMemoSound bits encode (rankedBitProgramValue rank program)
                (rankedBitMemoEvaluate rank program bits encode child.val previous).memory := by
          intro child previous hp
          exact ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous hp
        have hr := BitQuery.runMemo_sound
          (fun child : {child : κ // rank child < rank key} => rankedBitProgramValue rank program child.val)
          (bitMemoSound bits encode (rankedBitProgramValue rank program))
          (fun child previous => rankedBitMemoEvaluate rank program bits encode child.val previous)
          hchildren (program key) memory hmem
        have hv : (BitQuery.runMemo
            (fun child previous => rankedBitMemoEvaluate rank program bits encode child.val previous)
            (program key) memory).value = rankedBitProgramValue rank program key := by
          rw [rankedBitProgramValue]
          exact hr.1
        simp only [BinaryMemo.insertCosted_spec]
        refine ⟨hv, ?_⟩
        rw [hv]
        exact bitMemoSound_insert bits encode hinjective hbounded _ _ hr.2 key
  exact hall (rank key) key rfl memory hmemory

end EditApproximation

end OAI
