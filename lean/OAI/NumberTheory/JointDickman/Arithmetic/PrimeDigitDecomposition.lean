import OAI.NumberTheory.JointDickman.Arithmetic.HigherPrimeDigits

namespace OAI

/-! # Uniform prime-square residues split into two uniform digits -/

namespace JointDickman
open Finset

noncomputable def primeDigits (p : ℕ) (x : ZMod (p^2)) : ZMod p × ZMod p :=
  ((x.val : ZMod p), (x.val/p : ZMod p))

noncomputable def joinPrimeDigits (p : ℕ) (x : ZMod p × ZMod p) : ZMod (p^2) :=
  (x.1.val+p*x.2.val : ℕ)

theorem primeDigits_join {p : ℕ} [NeZero p] (x : ZMod p × ZMod p) :
    primeDigits p (joinPrimeDigits p x) = x := by
  have hp : 0 < p := NeZero.pos p
  have hb : x.1.val+p*x.2.val < p^2 := by
    have h1 := x.1.val_lt
    have h2 := x.2.val_lt
    nlinarith
  unfold primeDigits joinPrimeDigits
  rw [ZMod.val_natCast_of_lt hb]
  apply Prod.ext
  · simp
  · rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt x.1.val_lt, zero_add]
    exact ZMod.natCast_zmod_val _

theorem join_primeDigits {p : ℕ} [NeZero p] (x : ZMod (p^2)) :
    joinPrimeDigits p (primeDigits p x) = x := by
  have hp : 0 < p := NeZero.pos p
  have hq : x.val/p < p := (Nat.div_lt_iff_lt_mul hp).mpr (by
    simpa only [pow_two] using x.val_lt)
  unfold joinPrimeDigits primeDigits
  rw [ZMod.val_natCast, ZMod.val_natCast_of_lt hq, Nat.mod_add_div]
  exact ZMod.natCast_zmod_val _

noncomputable def primeDigitEquiv (p : ℕ) [NeZero p] :
    ZMod (p^2) ≃ ZMod p × ZMod p where
  toFun := primeDigits p
  invFun := joinPrimeDigits p
  left_inv := join_primeDigits
  right_inv := primeDigits_join

/-- The complete residue law, including any dependence on both digits. -/
theorem primeSquare_digit_mean {p : ℕ} [NeZero p]
    (F : ZMod p → ZMod p → ℝ) :
    (∑ x : ZMod (p^2), F (primeDigits p x).1 (primeDigits p x).2)/(p : ℝ)^2 =
      (∑ r : ZMod p, ∑ t : ZMod p, F r t)/(p : ℝ)^2 := by
  congr 1
  have h := (primeDigitEquiv p).sum_comp (fun x => F x.1 x.2)
  exact h.trans (Fintype.sum_prod_type _)

/-- First-digit events do not alter the conditional distribution of the
second digit. This is a finite sum identity, requiring no conditional measure. -/
theorem primeSquare_first_digit_test {p : ℕ} [NeZero p]
    (f : ZMod p → ℝ) (g : ZMod p → ZMod p → ℝ) :
    (∑ x : ZMod (p^2), f (primeDigits p x).1 *
      g (primeDigits p x).1 (primeDigits p x).2)/(p : ℝ)^2 =
      ∑ r : ZMod p, (f r/(p : ℝ))*((∑ t : ZMod p, g r t)/(p : ℝ)) := by
  rw [primeSquare_digit_mean (fun r t => f r * g r t)]
  simp_rw [← mul_sum]
  rw [sum_div]
  apply sum_congr rfl
  intro r _
  ring

end JointDickman

end OAI
