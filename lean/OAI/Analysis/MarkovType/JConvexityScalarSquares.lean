import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

theorem normalized_sum_sub_one_sq {n : ℕ} (a : Fin n → ℝ)
    (ha : (∑ j, a j) = (n : ℝ)) :
    (∑ j, (a j - 1) ^ 2) = (∑ j, a j ^ 2) - (n : ℝ) := by
  calc
    (∑ j, (a j - 1) ^ 2) = ∑ j, (a j ^ 2 - 2 * a j + 1) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ j, a j ^ 2) - 2 * (∑ j, a j) + (n : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp
    _ = (∑ j, a j ^ 2) - (n : ℝ) := by
      rw [ha]
      ring

theorem card_le_sum_sq_of_sum_eq {n : ℕ} (a : Fin n → ℝ)
    (ha : (∑ j, a j) = (n : ℝ)) :
    (n : ℝ) ≤ ∑ j, a j ^ 2 := by
  have hnonneg : 0 ≤ ∑ j, (a j - 1) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [normalized_sum_sub_one_sq a ha] at hnonneg
  linarith

theorem card_add_sq_le_sum_sq_of_one_add_le {n : ℕ} (a : Fin n → ℝ)
    (ha : (∑ j, a j) = (n : ℝ)) (k : Fin n) {ε : ℝ}
    (hε : 0 ≤ ε) (hk : 1 + ε ≤ a k) :
    (n : ℝ) + ε ^ 2 ≤ ∑ j, a j ^ 2 := by
  have hterm : (a k - 1) ^ 2 ≤ ∑ j, (a j - 1) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (a j - 1)) (Finset.mem_univ k)
  have hprod : 0 ≤ (a k - 1 - ε) * (a k - 1 + ε) :=
    mul_nonneg (by linarith) (by linarith)
  rw [normalized_sum_sub_one_sq a ha] at hterm
  nlinarith

theorem sq_sum_le_card_mul_sum_sq {n : ℕ} (a : Fin n → ℝ) :
    (∑ j, a j) ^ 2 ≤ (n : ℝ) * ∑ j, a j ^ 2 := by
  simpa using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin n => (1 : ℝ)) a

theorem sum_le_card_sub_one_mul_add {n : ℕ} (f : Fin n → ℝ) (k : Fin n)
    {A B : ℝ} (hbound : ∀ i, f i ≤ B) (hk : f k ≤ A) :
    (∑ i, f i) ≤ ((n : ℝ) - 1) * B + A := by
  have hsum := Finset.sum_erase_add Finset.univ f (Finset.mem_univ k)
  have hconstant : (∑ i ∈ Finset.univ.erase k, B) + B = (n : ℝ) * B := by
    simpa using
      Finset.sum_erase_add Finset.univ (fun _ : Fin n => B) (Finset.mem_univ k)
  have hle : (∑ i ∈ Finset.univ.erase k, f i) ≤
      ∑ i ∈ Finset.univ.erase k, B :=
    Finset.sum_le_sum fun i _ => hbound i
  calc
    (∑ i, f i) = (∑ i ∈ Finset.univ.erase k, f i) + f k := hsum.symm
    _ ≤ (∑ i ∈ Finset.univ.erase k, B) + A := add_le_add hle hk
    _ = ((n : ℝ) - 1) * B + A := by linarith

end MarkovSuperreflexivity

end OAI
