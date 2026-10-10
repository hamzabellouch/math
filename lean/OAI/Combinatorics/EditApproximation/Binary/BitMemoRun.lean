import OAI.Combinatorics.EditApproximation.Binary.BitMemoMap
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Execution of charged adaptive queries on actual binary-word memos.
The rational view is used only to prove preservation of the
memo trace; Boolean local work is retained as an additional counter. -/

namespace EditApproximation



def BitRecursiveMemoResult.decode {κ : Type*} (result : BitRecursiveMemoResult κ) :
    RecursiveMemoResult κ :=
  ⟨result.value.value, result.memory.mapValues BinaryFraction.value,
    result.freshKeys, result.dictionaryVisits, result.requests⟩

namespace BitQuery



theorem runMemo_decode {ι κ : Type*}
    (ask : ι → BinaryMemo BinaryFraction → BitRecursiveMemoResult κ)
    (expectedAsk : ι → BinaryMemo ℚ → RecursiveMemoResult κ)
    (hask : ∀ key memory, (ask key memory).decode =
      expectedAsk key (memory.mapValues BinaryFraction.value))
    {program : BitQuery ι BinaryFraction} {expected : FiniteQuery ι}
    (h : Refines (fun word value => word.value = value) program expected)
    (memory : BinaryMemo BinaryFraction) :
    (runMemo ask program memory).decode =
      FiniteQuery.run expectedAsk expected (memory.mapValues BinaryFraction.value) := by
  induction h generalizing memory with
  | done h =>
    simp only [runMemo, FiniteQuery.run, BitRecursiveMemoResult.decode, h]
  | charge steps h ih => exact ih memory
  | read key next expected h ih =>
    have hf := hask key memory
    have hvalue := congrArg RecursiveMemoResult.value hf
    have hmemory := congrArg RecursiveMemoResult.memory hf
    have hfresh := congrArg RecursiveMemoResult.freshKeys hf
    have hdict := congrArg RecursiveMemoResult.dictionaryVisits hf
    have hrequests := congrArg RecursiveMemoResult.requests hf
    have hr := ih (ask key memory).value (ask key memory).memory
    unfold runMemo FiniteQuery.run
    dsimp only
    unfold BitRecursiveMemoResult.decode at hvalue hmemory hfresh hdict hrequests hr ⊢
    simp only at hvalue hmemory hfresh hdict hrequests
    rw [hvalue, hmemory] at hr
    rw [← hr]
    simp only [hfresh, hdict, hrequests]

end BitQuery
end EditApproximation

end OAI
