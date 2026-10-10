import OAI.NumberTheory.Ostmann.Arithmetic.AtomIntervalRanges

namespace OAI

/-! # The original interval guards have bounded complexity at every finite depth -/
namespace Ostmann
open scoped Classical

theorem atomIntervalRanges_singleton {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (lo hi : I → ℕ) (n : ℕ)
    (r : ScheduleAtomRange role n) (hr : r ∈ atomIntervalRanges role lo hi n) :
    r.atoms.length = 1 := by
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr
  rfl

theorem atomIntervalRanges_length_le {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (lo hi : I → ℕ) (k n : ℕ) (hn : n ≤ k) :
    (atomIntervalRanges role lo hi n).length ≤ 3 ^ k * Fintype.card I := by
  have he : (atomIntervalRanges role lo hi n).length = Fintype.card (CopyScheduleAtoms role n) := by
    simp only [atomIntervalRanges, List.length_map, Finset.length_toList, Finset.card_univ]
  rw [he]
  exact (copyScheduleAtoms_card_le role n).trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega : 1 ≤ 3) hn))

end Ostmann

end OAI
