import Mathlib

namespace OAI

/-! Finite index counts for the consecutive-block depth-five construction. -/

open scoped BigOperators

namespace Problem335

/-- A lower product gate chooses a block, its two endpoints, and all internal indices. -/
abbrev BlockLowerIndex (n r : ℕ) (d : Fin r → ℕ) :=
  Σ b : Fin r, Fin n × Fin n × (Fin (d b - 1) → Fin n)

/-- A middle sum gate computes one entry of one block product. -/
abbrev BlockMiddleIndex (n r : ℕ) := Fin r × Fin n × Fin n

/-- An upper product gate chooses the indices at the boundaries between blocks. -/
abbrev BlockUpperIndex (n r : ℕ) := Fin (r - 1) → Fin n

@[simp] theorem card_blockMiddleIndex (n r : ℕ) :
    Fintype.card (BlockMiddleIndex n r) = r * n ^ 2 := by
  simp [BlockMiddleIndex, pow_two]

@[simp] theorem card_blockUpperIndex (n r : ℕ) :
    Fintype.card (BlockUpperIndex n r) = n ^ (r - 1) := by
  simp [BlockUpperIndex]

/-- Count the monomials used for every entry of a nonempty block. -/
theorem block_entry_monomial_count (n d : ℕ) (hd : 1 ≤ d) :
    Fintype.card (Fin n × Fin n × (Fin (d - 1) → Fin n)) = n ^ (d + 1) := by
  have h : 2 + (d - 1) = d + 1 := by omega
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
  rw [← mul_assoc, ← pow_two, ← pow_add, h]

theorem card_blockLowerIndex (n r : ℕ) (d : Fin r → ℕ)
    (hd : ∀ b, 1 ≤ d b) :
    Fintype.card (BlockLowerIndex n r d) = ∑ b, n ^ (d b + 1) := by
  rw [Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun b _ => block_entry_monomial_count n (d b) (hd b))

/-- Uniform block-length bounds control the total number of lower gates. -/
theorem card_blockLowerIndex_le (n r t : ℕ) (d : Fin r → ℕ)
    (hn : 1 ≤ n) (hd : ∀ b, 1 ≤ d b) (hdt : ∀ b, d b ≤ t) :
    Fintype.card (BlockLowerIndex n r d) ≤ r * n ^ (t + 1) := by
  rw [card_blockLowerIndex n r d hd]
  calc
    ∑ b : Fin r, n ^ (d b + 1) ≤ ∑ _b : Fin r, n ^ (t + 1) := by
      exact Finset.sum_le_sum (fun b _ => pow_le_pow_right₀ hn (Nat.add_le_add_right (hdt b) 1))
    _ = r * n ^ (t + 1) := by simp

/-- The exact finite index counts give the advertised combinatorial gate bound. -/
theorem block_gate_count_le (n r t : ℕ) (d : Fin r → ℕ)
    (hn : 1 ≤ n) (hd : ∀ b, 1 ≤ d b) (hdt : ∀ b, d b ≤ t) :
    2 * n ^ 3 + Fintype.card (BlockLowerIndex n r d) +
        Fintype.card (BlockMiddleIndex n r) + Fintype.card (BlockUpperIndex n r) + 1 ≤
      2 * n ^ 3 + r * n ^ 2 + r * n ^ (t + 1) + n ^ (r - 1) + 1 := by
  rw [card_blockMiddleIndex, card_blockUpperIndex]
  have h := card_blockLowerIndex_le n r t d hn hd hdt
  omega

end Problem335

end OAI
