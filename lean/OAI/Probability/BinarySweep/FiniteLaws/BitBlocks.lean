import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma exists_bit_blocks (r : ℕ) (hr : 0<r) : ∀d : ℕ, r≤d →
    ∃b : ℕ, 1≤b ∧ ∃bits : Fin b → ℕ,
      (∀j,r≤bits j ∧ bits j≤2*r) ∧ ∑j,bits j=d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    by_cases hsmall : d≤2*r
    · refine ⟨1,by omega,fun _ => d,fun _ => ⟨hd,hsmall⟩,?_⟩
      simp
    obtain ⟨b,hb,bits,hbits,hsum⟩ := ih (d-r) (by omega) (by omega)
    refine ⟨b+1,by omega,Fin.cons r bits,?_,?_⟩
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [Fin.cons_zero]; omega
      · simpa using hbits i
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero,Fin.cons_succ,hsum,Nat.add_sub_of_le hd]

end BinaryCoordinateSweeps

end

end OAI
