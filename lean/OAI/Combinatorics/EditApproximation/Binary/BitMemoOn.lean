import OAI.Combinatorics.EditApproximation.Binary.BitQueryOn

namespace OAI

/-! Reachable-oracle simulation retains the exact memo trace while allowing
local output normalization justified by the actual grid invariant. -/

namespace EditApproximation.BitQuery

theorem runMemo_decode_on {ι κ : Type*} (oracle : ι → BinaryFraction)
    (invariant : BinaryMemo BinaryFraction → Prop)
    (ask : ι → BinaryMemo BinaryFraction → BitRecursiveMemoResult κ)
    (expectedAsk : ι → BinaryMemo ℚ → RecursiveMemoResult κ)
    (hask : ∀ key memory, invariant memory →
      (ask key memory).value = oracle key ∧ invariant (ask key memory).memory ∧
        (ask key memory).decode = expectedAsk key (memory.mapValues BinaryFraction.value))
    {program : BitQuery ι BinaryFraction} {expected : FiniteQuery ι}
    (h : RefinesOn oracle (fun word value => word.value = value) program expected)
    (memory : BinaryMemo BinaryFraction) (hmemory : invariant memory) :
    (runMemo ask program memory).decode =
      FiniteQuery.run expectedAsk expected (memory.mapValues BinaryFraction.value) ∧
        invariant (runMemo ask program memory).memory := by
  induction h generalizing memory with
  | done h =>
    exact ⟨by simp only [runMemo, FiniteQuery.run, BitRecursiveMemoResult.decode, h], hmemory⟩
  | charge steps h ih => exact ih memory hmemory
  | read key next expected h ih =>
    have hf := hask key memory hmemory
    have hvalue := congrArg RecursiveMemoResult.value hf.2.2
    have hmem := congrArg RecursiveMemoResult.memory hf.2.2
    have hfresh := congrArg RecursiveMemoResult.freshKeys hf.2.2
    have hdict := congrArg RecursiveMemoResult.dictionaryVisits hf.2.2
    have hrequests := congrArg RecursiveMemoResult.requests hf.2.2
    have hr := ih (ask key memory).memory hf.2.1
    rw [← hf.1] at hr
    refine ⟨?_, hr.2⟩
    unfold runMemo FiniteQuery.run
    dsimp only
    unfold BitRecursiveMemoResult.decode at hvalue hmem hfresh hdict hrequests hr ⊢
    simp only at hvalue hmem hfresh hdict hrequests
    rw [hvalue, hmem] at hr
    rw [← hr.1]
    simp only [hfresh, hdict, hrequests]

end EditApproximation.BitQuery

end OAI
