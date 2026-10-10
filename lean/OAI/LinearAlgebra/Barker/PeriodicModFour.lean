import OAI.LinearAlgebra.Barker.Model
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

namespace CirculantHadamard.Barker

open scoped BigOperators

def negativeBit {n : ℕ} (h : Fin n → ℤ) (j : Fin n) : ℤ :=
  if h j = -1 then 1 else 0

theorem sign_eq_one_sub_two_bit {n : ℕ} (h : Fin n → ℤ)
    (hs : ∀ j, IsSign (h j)) (j : Fin n) :
    h j = 1 - 2 * negativeBit h j := by
  rcases hs j with hj | hj <;> norm_num [negativeBit, hj]

def cyclicSubtractEquiv {n : ℕ} [NeZero n] (a : Fin n) : Fin n ≃ Fin n where
  toFun j := j - a
  invFun j := j + a
  left_inv j := sub_add_cancel j a
  right_inv j := add_sub_cancel_right j a

theorem sum_negativeBit_shift {n : ℕ} [NeZero n] (h : Fin n → ℤ) (a : Fin n) :
    (∑ j, negativeBit h (j - a)) = ∑ j, negativeBit h j := by
  exact (cyclicSubtractEquiv a).sum_comp (negativeBit h)

theorem periodic_bit_identity {n : ℕ} [NeZero n] (h : Fin n → ℤ)
    (hs : ∀ j, IsSign (h j)) (a : Fin n) :
    periodic h a = (n : ℤ) + 4 *
      ((∑ j, negativeBit h j * negativeBit h (j - a)) - ∑ j, negativeBit h j) := by
  have hterm (j : Fin n) : h j * h (j - a) =
      1 - 2 * negativeBit h j - 2 * negativeBit h (j - a) +
        4 * (negativeBit h j * negativeBit h (j - a)) := by
    rw [sign_eq_one_sub_two_bit h hs j, sign_eq_one_sub_two_bit h hs (j - a)]
    ring
  calc
    periodic h a = ∑ j : Fin n,
        (1 - 2 * negativeBit h j - 2 * negativeBit h (j - a) +
          4 * (negativeBit h j * negativeBit h (j - a))) := by
      unfold periodic
      exact Finset.sum_congr rfl (fun j _ => hterm j)
    _ = (n : ℤ) - 2 * (∑ j, negativeBit h j) -
        2 * (∑ j, negativeBit h (j - a)) +
        4 * (∑ j, negativeBit h j * negativeBit h (j - a)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp
    _ = _ := by rw [sum_negativeBit_shift]; ring

theorem periodic_mod_four {n : ℕ} [NeZero n] (h : Fin n → ℤ)
    (hs : ∀ j, IsSign (h j)) (a : Fin n) :
    (4 : ℤ) ∣ periodic h a - (n : ℤ) := by
  refine ⟨(∑ j, negativeBit h j * negativeBit h (j - a)) -
    ∑ j, negativeBit h j, ?_⟩
  rw [periodic_bit_identity h hs a]
  ring

end CirculantHadamard.Barker

end OAI
