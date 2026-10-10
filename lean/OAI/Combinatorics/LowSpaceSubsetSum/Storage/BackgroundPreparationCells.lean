import OAI.Combinatorics.LowSpaceSubsetSum.Storage.IntervalDomainCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.AllocationCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.BackgroundBlockCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationBackgroundPreparation

namespace OAI

/-! # Live storage for the allocated background construction

The scanned outside list is shared by all eight row copies. The six integer
width computations run before the size guard and are charged on both branches.
-/

noncomputable section
namespace LowSpaceSubsetSum.BackgroundPreparationCells

open scoped BigOperators
variable {n : ℕ}

private def assemble (outside : List (Fin n) × ℕ) (counts : Vector ℕ 8 × ℕ) :
    Option (Vector (List (Fin n)) 8) × ℕ :=
  if h : (∑ i : Fin 8, counts.1[i.val]) = outside.1.length then
    let xs : Vector (Fin n) outside.1.length := ⟨outside.1.toArray, by simp only [List.size_toArray]⟩
    let rows := StoredBackgroundBlocks.run xs counts.1 h
    (some rows.1, outside.2+counts.2+rows.2+20)
  else (none, outside.2+counts.2+20)

private def core (outside : (List (Fin n) × ℕ) × ℕ)
    (counts : (Vector ℕ 8 × ℕ) × ℕ) :
    (Option (Vector (List (Fin n)) 8) × ℕ) × ℕ :=
  if h : (∑ i : Fin 8, counts.1.1[i.val]) = outside.1.1.length then
    let xs : Vector (Fin n) outside.1.1.length := ⟨outside.1.1.toArray, by simp only [List.size_toArray]⟩
    let rows := BackgroundBlockCells.run xs counts.1.1 h
    ((some rows.1.1, outside.1.2+counts.1.2+rows.1.2+20),
      outside.2+counts.2+rows.2+12*n+128)
  else ((none, outside.1.2+counts.1.2+20), outside.2+counts.2+12*n+128)

private theorem core_value (outside : (List (Fin n) × ℕ) × ℕ)
    (counts : (Vector ℕ 8 × ℕ) × ℕ) :
    (core outside counts).1 = assemble outside.1 counts.1 := by
  unfold core assemble
  dsimp only
  split <;> simp only [BackgroundBlockCells.value]

def run (_I : Instance n) (v : Vector (Fin n) n) (guesses : Vector ℕ 3) :
    (Option (Vector (List (Fin n)) 8) × ℕ) × ℕ :=
  core (IntervalDomainCells.run v (3*mixerSize n) (n-3*mixerSize n))
    (AllocationCells.run n guesses)

theorem value (I : Instance n) (v : Vector (Fin n) n) (guesses : Vector ℕ 3) :
    (run I v guesses).1 = RepresentationBackgroundPreparation.run I v guesses := by
  have ho : (IntervalDomainCells.run v (3*mixerSize n) (n-3*mixerSize n)).1 =
      CanonicalBackground.run v := IntervalDomainCells.run_value v _ _
  calc
    (run I v guesses).1 = assemble
        (IntervalDomainCells.run v (3*mixerSize n) (n-3*mixerSize n)).1
        (AllocationCells.run n guesses).1 := core_value _ _
    _ = assemble (CanonicalBackground.run v)
        (RepresentationAllocationExecution.run n guesses) :=
      congrArg₂ assemble ho (AllocationCells.value n guesses)
    _ = RepresentationBackgroundPreparation.run I v guesses := rfl

theorem cells (I : Instance n) (v : Vector (Fin n) n) (guesses : Vector ℕ 3) :
    (run I v guesses).2 ≤ 2048*(n+1)^2 := by
  have ho := IntervalDomainCells.run_cells v (3*mixerSize n) (n-3*mixerSize n)
  have hc := AllocationCells.cells n guesses
  have hl : (IntervalDomainCells.run v (3*mixerSize n) (n-3*mixerSize n)).1.1.length ≤ n := by
    rw [IntervalDomainCells.run_value]
    exact CanonicalBackground.length_le v
  unfold run core
  dsimp only
  split
  next h =>
    have hr := BackgroundBlockCells.cells
      (⟨(IntervalDomainCells.run v (3*mixerSize n) (n-3*mixerSize n)).1.1.toArray,
        by simp only [List.size_toArray]⟩)
      (AllocationCells.run n guesses).1.1 h
    change _+_+_+12*n+128 ≤ _
    nlinarith only [ho, hc, hl, hr, Nat.zero_le (n^2)]
  · change _+_+12*n+128 ≤ _
    nlinarith only [ho, hc, Nat.zero_le (n^2)]

end LowSpaceSubsetSum.BackgroundPreparationCells

end

end OAI
