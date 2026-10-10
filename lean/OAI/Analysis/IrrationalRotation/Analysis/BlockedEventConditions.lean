import OAI.Analysis.IrrationalRotation.Couplings.BlockedProductCoupling

namespace OAI

open Set

namespace Invariant233.BlockedProductCoupling

theorem not_mem_futureBad_iff {m : ℕ → ℕ} {K : ℕ → ℝ}
    {j : ℕ} {z : Sample m} :
    z ∉ futureBad m K j ↔
      ∀ s, j < s → ∀ i : Fin (m s),
        (z s i).2.1 < 1 - 2 * K j / ((m s : ℝ) * K s) ∧
        2 * K j / ((m s : ℝ) * K s) < (z s i).2.2 := by
  simp only [futureBad, mem_iUnion, mem_ofPred_eq, not_exists, not_or, not_le]
  constructor
  · intro h s hs
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hs)
    subst s
    exact h n
  · intro h n i
    exact h (j + 1 + n) (by omega) i

theorem mem_retainedEvent_iff {X : Type*} {m : ℕ → ℕ} {K : ℕ → ℝ}
    {r : X → ℝ} {x y : Sample m → X} {j : ℕ} {z : Sample m} :
    z ∈ retainedEvent m K r x y j ↔
      (∃ i, (z j i).1 = some (4 : Fin 5)) ∧
      (∀ i, (z j i).2.1 < 1 - 2 / (m j : ℝ) ∧
        2 / (m j : ℝ) < (z j i).2.2) ∧
      (∀ s, j < s → ∀ i : Fin (m s),
        (z s i).2.1 < 1 - 2 * K j / ((m s : ℝ) * K s) ∧
        2 * K j / ((m s : ℝ) * K s) < (z s i).2.2) ∧
      1 / (j : ℝ) ≤ r (x z) ∧ 1 / (j : ℝ) ≤ 1 - r (y z) := by
  simp only [retainedEvent, mem_sdiff, mem_union, not_or, not_mem_futureBad_iff,
    currentEvent, mem_ofPred_eq, not_lt]
  tauto

end Invariant233.BlockedProductCoupling

end OAI
