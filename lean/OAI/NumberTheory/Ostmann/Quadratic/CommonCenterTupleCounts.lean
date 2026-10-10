import Mathlib.Data.Fintype.CardEmbedding
import OAI.NumberTheory.Ostmann.Quadratic.CommonCenterAssembly

namespace OAI

/-! # Ordered distinct tuples and common-center lift moments -/

namespace Ostmann

open scoped BigOperators

/-- An ordered tuple of distinct primes lies in a matching set exactly when
it is an embedding into that set. -/
def matchingTupleEquiv {P : Type*} (S : Finset P) (r : ℕ) :
    (Fin r ↪ S) ≃ {e : Fin r ↪ P // ∀ i, e i ∈ S} where
  toFun e := ⟨⟨fun i => (e i).1, fun i j h => e.injective (Subtype.ext h)⟩,
    fun i => (e i).2⟩
  invFun e := ⟨fun i => ⟨e.1 i, e.2 i⟩, fun i j h => e.1.injective (congrArg Subtype.val h)⟩
  left_inv e := by ext i; rfl
  right_inv e := by apply Subtype.ext; ext i; rfl

theorem card_matchingTuple {P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (r : ℕ) :
    Fintype.card {e : Fin r ↪ P // ∀ i, e i ∈ S} = S.card.descFactorial r := by
  rw [← Fintype.card_congr (matchingTupleEquiv S r), Fintype.card_embedding_eq]
  simp only [Fintype.card_coe, Fintype.card_fin]

private def incidenceSwap {N E : Type*} (R : N → E → Prop) :
    (Σ n, {e // R n e}) ≃ (Σ e, {n // R n e}) where
  toFun z := ⟨z.2.1, z.1, z.2.2⟩
  invFun z := ⟨z.2.1, z.1, z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact double counting of all ordered distinct tuple/lift incidences. -/
theorem sum_matching_factorials {N P : Type*} [Fintype N] [Fintype P] [DecidableEq P]
    (S : N → Finset P) (r : ℕ) :
    (∑ n, (S n).card.descFactorial r) =
      ∑ e : Fin r ↪ P, Fintype.card {n : N // ∀ i, e i ∈ S n} := by
  classical
  have h := Fintype.card_congr (incidenceSwap (fun n (e : Fin r ↪ P) => ∀ i, e i ∈ S n))
  simp only [Fintype.card_sigma, card_matchingTuple] at h
  exact h

/-- A uniform bound on the number of lifts of each tuple gives the lower-order
factorial-moment upper bound used by common-center extraction. -/
theorem sum_matching_factorials_le {N P : Type*} [Fintype N] [Fintype P] [DecidableEq P]
    (S : N → Finset P) (r C : ℕ)
    (hcount : ∀ e : Fin r ↪ P, Fintype.card {n : N // ∀ i, e i ∈ S n} ≤ C) :
    (∑ n, (S n).card.descFactorial r) ≤ (Fintype.card P).descFactorial r * C := by
  classical
  rw [sum_matching_factorials]
  calc
    _ ≤ ∑ _e : Fin r ↪ P, C := Finset.sum_le_sum fun e _ => hcount e
    _ = _ := by simp

/-- A family of distinct tuples each admitting a lift supplies the high
factorial-moment lower bound; no unique-lift assumption is required. -/
theorem card_tuples_le_sum_matching_factorials {N P : Type*}
    [Fintype N] [Fintype P] [DecidableEq P]
    (S : N → Finset P) (r : ℕ) (E : Finset (Fin r ↪ P))
    (hlift : ∀ e ∈ E, ∃ n, ∀ i, e i ∈ S n) :
    E.card ≤ ∑ n, (S n).card.descFactorial r := by
  classical
  rw [sum_matching_factorials]
  calc
    E.card = ∑ _e ∈ E, 1 := by simp
    _ ≤ ∑ e ∈ E, Fintype.card {n : N // ∀ i, e i ∈ S n} := by
      apply Finset.sum_le_sum
      intro e he
      obtain ⟨n, hn⟩ := hlift e he
      have : Nonempty {n : N // ∀ i, e i ∈ S n} := ⟨⟨n, hn⟩⟩
      exact Fintype.card_pos_iff.mpr this
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E) (by simp)

end Ostmann

end OAI
