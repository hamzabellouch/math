import Mathlib

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open Finset

noncomputable def intervalPrimes (x H : ℝ) (q : ℕ) (r : ℤ) : Finset ℕ :=
  (range (⌊max (x+H) 0⌋₊+1)).filter (fun p =>
    p.Prime ∧ x < (p:ℝ) ∧ (p:ℝ) ≤ x+H ∧ Int.ModEq (q:ℤ) (p:ℤ) r)

theorem mem_intervalPrimes (x H : ℝ) (q : ℕ) (r : ℤ) (p : ℕ) :
    p ∈ intervalPrimes x H q r ↔
      p.Prime ∧ x < (p:ℝ) ∧ (p:ℝ) ≤ x+H ∧ Int.ModEq (q:ℤ) (p:ℤ) r := by
  constructor
  · intro h
    exact (mem_filter.mp h).2
  · intro h
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (Nat.lt_succ_of_le ?_),h⟩
    exact (Nat.le_floor_iff (le_max_right _ _)).mpr (h.2.2.1.trans (le_max_left _ _))

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
