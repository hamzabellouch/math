import OAI.Combinatorics.BinaryEdit.Model
import Mathlib

namespace OAI

namespace TreeEdit.BinaryLower.FiniteAlphabet

open scoped BigOperators

/-- The original (pre-encoding) word length already dominates the tree
parameter. This lets any absolute code threshold be met by increasing `k`. -/
theorem parameter_le_word_length {k : ℕ} (hk : 0 < k) :
    k ≤ (20 * k * k ^ (20 * k)) ^ k := by
  have hp : 1 ≤ k ^ (20 * k) := Nat.one_le_pow _ _ hk
  have hb : k ≤ 20 * k * k ^ (20 * k) := by
    have h := Nat.mul_le_mul_left (20 * k) hp
    nlinarith
  exact hb.trans (Nat.le_pow hk)

/-- Explicit simultaneous threshold for the original word length and `k≥2`. -/
theorem code_threshold (M₀ : ℕ) :
    ∀ k ≥ max 2 M₀, 2 ≤ k ∧ M₀ ≤ (20 * k * k ^ (20 * k)) ^ k := by
  intro k hk
  have hk2 : 2 ≤ k := (le_max_left 2 M₀).trans hk
  refine ⟨hk2, ?_⟩
  exact ((le_max_right 2 M₀).trans hk).trans (parameter_le_word_length (by omega))

/-- The numerical alphabet budget holds already for every `k≥2`. -/
theorem residue_budget_le_word_length {k : ℕ} (hk : 2 ≤ k) :
    (20 * k) ^ k * (2 * k ^ (5 * k)) ≤ (20 * k * k ^ (20 * k)) ^ k := by
  rw [mul_pow (20 * k) (k ^ (20 * k)) k]
  apply Nat.mul_le_mul_left
  calc
    2 * k ^ (5 * k) ≤ k * k ^ (5 * k) := Nat.mul_le_mul_right _ hk
    _ = k ^ (5 * k + 1) := by rw [pow_succ, Nat.mul_comm]
    _ ≤ (k ^ (20 * k)) ^ k := by
      rw [← pow_mul]
      apply Nat.pow_le_pow_right (by omega)
      nlinarith

/-- Bounding each factor bounds the leaf period from the manuscript. -/
theorem leaf_period_le {m k : ℕ} (p : Fin k → Fin m → ℕ)
    (hupper : ∀ q i, p q i ≤ k ^ 5) (a : Fin k → Fin m) :
    2 * (∏ q, p q (a q)) ≤ 2 * k ^ (5 * k) := by
  apply Nat.mul_le_mul_left
  calc
    (∏ q, p q (a q)) ≤ ∏ _q : Fin k, k ^ 5 :=
      Finset.prod_le_prod fun q _ => hupper q (a q)
    _ = k ^ (5 * k) := by simp [← pow_mul]

/-- Positivity of every factor makes every leaf modulus nonzero. -/
theorem leaf_period_pos {m k : ℕ} (p : Fin k → Fin m → ℕ)
    (hpos : ∀ q i, 0 < p q i) (a : Fin k → Fin m) :
    0 < 2 * (∏ q, p q (a q)) := by
  apply Nat.mul_pos (by decide)
  exact Finset.prod_pos fun q _ => hpos q (a q)

/-- Bound the tagged residue alphabet on literal fixed-length leaf words.
The local Fintype instances are constructed here, rather than presupposed. -/
theorem tagged_alphabet_card_le {m k H : ℕ}
    (Q : Word (Fin m) k → ℕ)
    (hQpos : ∀ a, 0 < Q a) (hQupper : ∀ a, Q a ≤ H) :
    Nat.card (Σ a : Word (Fin m) k, ZMod (Q a)) ≤ m ^ k * H := by
  classical
  let : Fintype (Word (Fin m) k) :=
    Fintype.ofEquiv (Fin k → Fin m) (Equiv.vectorEquivFin (Fin m) k).symm
  let (a : Word (Fin m) k) : NeZero (Q a) := ⟨Nat.ne_of_gt (hQpos a)⟩
  have hleaf : Fintype.card (Word (Fin m) k) = m ^ k := by
    let e : Word (Fin m) k ≃ (Fin k → Fin m) := Equiv.vectorEquivFin (Fin m) k
    calc
      Fintype.card (Word (Fin m) k) = Fintype.card (Fin k → Fin m) := Fintype.card_congr e
      _ = m ^ k := by simp
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp_rw [ZMod.card]
  calc
    (∑ a, Q a) ≤ ∑ _a : Word (Fin m) k, H :=
      Finset.sum_le_sum fun a _ => hQupper a
    _ = m ^ k * H := by simp [hleaf]

/-- The literal tagged residue alphabet satisfies the cardinal hypotheses of
the fixed-length binary conversion theorem. -/
theorem finite_tree_alphabet_bounds {k : ℕ} (hk : 2 ≤ k)
    (Q : Word (Fin (20 * k)) k → ℕ)
    (hQpos : ∀ a, 0 < Q a) (hQupper : ∀ a, Q a ≤ 2 * k ^ (5 * k)) :
    Finite (Σ a : Word (Fin (20 * k)) k, ZMod (Q a)) ∧
    1 ≤ Nat.card (Σ a : Word (Fin (20 * k)) k, ZMod (Q a)) ∧
    Nat.card (Σ a : Word (Fin (20 * k)) k, ZMod (Q a)) ≤
      (20 * k * k ^ (20 * k)) ^ k := by
  classical
  let : Fintype (Word (Fin (20 * k)) k) :=
    Fintype.ofEquiv (Fin k → Fin (20 * k))
      (Equiv.vectorEquivFin (Fin (20 * k)) k).symm
  let (a : Word (Fin (20 * k)) k) : NeZero (Q a) := ⟨Nat.ne_of_gt (hQpos a)⟩
  let a : Word (Fin (20 * k)) k :=
    ⟨List.replicate k ⟨0, by omega⟩, by simp⟩
  let : Nonempty (Σ a : Word (Fin (20 * k)) k, ZMod (Q a)) := ⟨⟨a, 0⟩⟩
  refine ⟨inferInstance, Nat.card_pos, ?_⟩
  exact (tagged_alphabet_card_le Q hQpos hQupper).trans
    (residue_budget_le_word_length hk)

/-- Specialization to the source's products of one prime from each depth.
Only positivity and the upper prime-size bound are needed for cardinality. -/
theorem prime_product_alphabet_bounds {k : ℕ} (hk : 2 ≤ k)
    (p : Fin k → Fin (20 * k) → ℕ)
    (hpos : ∀ q i, 0 < p q i) (hupper : ∀ q i, p q i ≤ k ^ 5) :
    let Q : Word (Fin (20 * k)) k → ℕ := fun a =>
      2 * ∏ q, p q ((Equiv.vectorEquivFin (Fin (20 * k)) k a) q)
    Finite (Σ a : Word (Fin (20 * k)) k, ZMod (Q a)) ∧
    1 ≤ Nat.card (Σ a : Word (Fin (20 * k)) k, ZMod (Q a)) ∧
    Nat.card (Σ a : Word (Fin (20 * k)) k, ZMod (Q a)) ≤
      (20 * k * k ^ (20 * k)) ^ k := by
  apply finite_tree_alphabet_bounds hk
  · intro a
    exact leaf_period_pos p hpos _
  · intro a
    exact leaf_period_le p hupper _

end TreeEdit.BinaryLower.FiniteAlphabet

end OAI
