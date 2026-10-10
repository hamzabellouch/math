import OAI.Combinatorics.EditApproximation.Binary.BitMemoSound

namespace OAI

/-! Simulation along a fixed reachable oracle. This allows a checked
normalization at the end of a local query: its denominator invariant is
required only for the values that the ranked execution actually reaches. -/

namespace EditApproximation.BitQuery

inductive RefinesOn {ι β : Type*} (oracle : ι → BinaryFraction) (relation : β → ℚ → Prop) :
    BitQuery ι β → FiniteQuery ι → Prop where
  | done {result : β} {expected : ℚ} (h : relation result expected) :
      RefinesOn oracle relation (.done result) (.done expected)
  | read (key : ι) (next : BinaryFraction → BitQuery ι β) (expected : ℚ → FiniteQuery ι)
      (h : RefinesOn oracle relation (next (oracle key)) (expected (oracle key).value)) :
      RefinesOn oracle relation (.read key next) (.read key expected)
  | charge (steps : ℕ) {program : BitQuery ι β} {expected : FiniteQuery ι}
      (h : RefinesOn oracle relation program expected) :
      RefinesOn oracle relation (.charge steps program) expected

theorem Refines.onOracle {ι β : Type*} {relation : β → ℚ → Prop}
    {program : BitQuery ι β} {expected : FiniteQuery ι}
    (h : Refines relation program expected) (oracle : ι → BinaryFraction) :
    RefinesOn oracle relation program expected := by
  induction h with
  | done h => exact .done h
  | charge steps _ ih => exact .charge steps ih
  | read key next expected _ ih => exact .read key next expected (ih (oracle key))

theorem RefinesOn.value_keys {ι β : Type*} {oracle : ι → BinaryFraction} {relation : β → ℚ → Prop}
    {program : BitQuery ι β} {expected : FiniteQuery ι}
    (h : RefinesOn oracle relation program expected) :
    relation (program.value oracle) (expected.value (fun key => (oracle key).value)) ∧
      program.keys oracle = expected.keys (fun key => (oracle key).value) := by
  induction h with
  | done h => exact ⟨h, rfl⟩
  | charge steps _ ih => exact ih
  | read key next expected _ ih => exact ⟨ih.1, congrArg (List.cons key) ih.2⟩

theorem RefinesOn.finish {ι : Type*} {oracle : ι → BinaryFraction}
    {program : BitQuery ι BinaryFraction} {expected : FiniteQuery ι}
    (h : RefinesOn oracle (fun word value => word.value = value) program expected)
    (finish : BinaryFraction → BinaryFraction × ℕ)
    (hf : (finish (program.value oracle)).1.value = (program.value oracle).value) :
    RefinesOn oracle (fun word value => word.value = value)
      (program.bind fun word => compute (finish word)) expected := by
  induction h with
  | done h => exact .charge _ (.done (hf.trans h))
  | charge steps _ ih => exact .charge steps (ih hf)
  | read key next expected _ ih => exact .read key _ _ (ih hf)

end EditApproximation.BitQuery

end OAI
