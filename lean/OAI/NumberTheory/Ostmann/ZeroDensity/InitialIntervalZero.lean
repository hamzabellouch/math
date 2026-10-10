import OAI.NumberTheory.Ostmann.Arithmetic.AtomIntervalRanges

namespace OAI

/-! # A nontrivial original interval removes the initial zero frequency -/
namespace Ostmann
open scoped Classical

theorem fullAtomTransferWeight_zero_of_interval {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (lo hi : I → ℕ)
    (childBound pivotBound : ℕ → ℕ) (leaf : ScheduleAtomState role → ℤ → ℂ)
    (i : I) (hi₁ : 1 < lo i) (x : CopyScheduleAtoms role 0 → ℕ) :
    fullAtomTransferWeight role childBound pivotBound (atomIntervalRanges role lo hi)
      leaf 0 x (0 : ℤ) = 0 := by
  by_contra h
  have hu := (fullAtomTransferWeight_top_support role childBound pivotBound
    (atomIntervalRanges role lo hi) leaf 0 x (0 : ℤ) h).2 ⟨i, trivial⟩
  have he : x ⟨i, trivial⟩ = 1 := by
    simpa only [frequencyRoot, Int.natAbs_zero, Nat.coprime_zero_right] using hu
  have hr := (atomIntervalRanges_holds_iff role lo hi 0 x).mp
    (fun r hr => fullAtomTransferWeight_top_range role childBound pivotBound
      (atomIntervalRanges role lo hi) leaf 0 x (0 : ℤ) h r hr)
  have hl := (hr ⟨i, trivial⟩).1
  change lo i ≤ x ⟨i, trivial⟩ at hl
  omega

end Ostmann

end OAI
