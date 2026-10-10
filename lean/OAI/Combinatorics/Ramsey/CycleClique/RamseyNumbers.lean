import OAI.Combinatorics.Ramsey.CycleClique.Basic

namespace OAI

/-! Least forcing orders and the cycle–clique Ramsey number. -/

namespace CycleClique

/-- The exact least order forcing a cycle or a complementary clique. -/
def IsRamseyNumber (m n N : ℕ) : Prop :=
  RamseyProperty m n N ∧ ∀ M < N, ¬ RamseyProperty m n M

theorem cycleCliqueRamsey_eq_of_isRamseyNumber {m n N : ℕ}
    (h : IsRamseyNumber m n N) : cycleCliqueRamsey m n = N := by
  apply Nat.le_antisymm
  · exact Nat.sInf_le h.1
  · have hmem : RamseyProperty m n (cycleCliqueRamsey m n) :=
      Nat.sInf_mem (s := {M : ℕ | RamseyProperty m n M}) ⟨N, h.1⟩
    by_contra hlt
    exact h.2 _ (by omega) hmem

end CycleClique

end OAI
