import Mathlib.Data.Nat.Choose.Bounds
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularTemplate
import OAI.NumberTheory.Ostmann.Construction.BadMatchingHarmonicBudget

namespace OAI

/-! # The full factorial cost with the original bulk harmonic masses -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingRegular_inverse_mass_bound (n s m : ℕ)
    (mass : MovingRegularSlot n s m → ℝ) (L C : ℝ) (hL : 0 < L)
    (hsmall : ∀ j : TreeLeafIndex n × Fin s, Real.exp (-C * L) ≤ mass (j.1, .inl j.2))
    (hbulk : ∀ j : TreeLeafIndex n × Fin m, L ≤ mass (j.1, .inr j.2)) :
    (∏ i, (mass i)⁻¹) ≤
      (L⁻¹) ^ (2 ^ n * m) * Real.exp (C * L * (2 ^ n * s : ℕ)) := by
  have hpoint (j : TreeLeafIndex n) (i : Fin s ⊕ Fin m) :
      (mass (j, i))⁻¹ ≤ Sum.elim (fun _ => Real.exp (C * L)) (fun _ => L⁻¹) i := by
    cases i with
    | inl i =>
      have h := one_div_le_one_div_of_le (Real.exp_pos (-C * L)) (hsmall (j, i))
      simpa only [Sum.elim_inl, one_div, show -C * L = -(C * L) by ring, Real.exp_neg, inv_inv] using h
    | inr i => simpa only [Sum.elim_inr, one_div] using one_div_le_one_div_of_le hL (hbulk (j, i))
  have hnonneg (i : MovingRegularSlot n s m) : 0 ≤ (mass i)⁻¹ := by
    rcases i with ⟨j, i | i⟩
    · exact inv_nonneg.mpr ((Real.exp_pos _).le.trans (hsmall (j, i)))
    · exact inv_nonneg.mpr (hL.le.trans (hbulk (j, i)))
  apply (Finset.prod_le_prod₀ (fun i _ => hnonneg i) (fun i _ => hpoint i.1 i.2)).trans_eq
  rw [Fintype.prod_prod_type]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, card_treeLeafIndex]
  rw [mul_pow, ← pow_mul, ← pow_mul, ← Real.exp_nat_mul]
  push_cast
  rw [show (s : ℝ) * 2 ^ n * (C * L) = C * L * (2 ^ n * s) by ring]
  ring

theorem factorial_split_upper (N S : ℕ) :
    ((N + S).factorial : ℝ) ≤ 2 ^ (N + S) * (N.factorial : ℝ) * (S.factorial : ℝ) := by
  have h := Nat.mul_le_mul_right (S.factorial)
    (Nat.mul_le_mul_right (N.factorial) (Nat.choose_le_two_pow (N + S) N))
  have hf : (N + S).choose N * N.factorial * S.factorial = (N + S).factorial := by
    simpa only [Nat.add_sub_cancel_left] using
      Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right N S)
  rw [hf] at h
  exact_mod_cast h

theorem movingRegular_factorial_harmonic_bound (n s m : ℕ)
    (mass : MovingRegularSlot n s m → ℝ) (L z C : ℝ) (hL : 0 < L) (hz : 0 < z)
    (hm : (m : ℝ) ≤ z * L)
    (hsmall : ∀ j : TreeLeafIndex n × Fin s, Real.exp (-C * L) ≤ mass (j.1, .inl j.2))
    (hbulk : ∀ j : TreeLeafIndex n × Fin m, L ≤ mass (j.1, .inr j.2)) :
    ((Fintype.card (MovingRegularSlot n s m)).factorial : ℝ) * (∏ i, (mass i)⁻¹) ≤
      (2 : ℝ) ^ (2 ^ n * s) * ((2 ^ n * s).factorial : ℝ) *
        Real.exp (C * L * (2 ^ n * s : ℕ)) *
        Real.exp ((Real.log 2 + Real.log z + Real.log (2 ^ n : ℕ)) * (2 ^ n * m : ℕ)) := by
  have hf := factorial_split_upper (2 ^ n * m) (2 ^ n * s)
  have hp := movingRegular_inverse_mass_bound n s m mass L C hL hsmall hbulk
  have hnorm := factorial_harmonic_entropy 1 (2 ^ n * m) L ((2 ^ n : ℕ) * z) hL
    (mul_pos (by positivity) hz) (by
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ 2 ^ n by positivity)])
  simp only [pow_one, one_mul] at hnorm
  have hp0 : 0 ≤ ∏ i, (mass i)⁻¹ := by
    apply Finset.prod_nonneg
    rintro ⟨j, i | i⟩ _
    · exact inv_nonneg.mpr ((Real.exp_pos _).le.trans (hsmall (j, i)))
    · exact inv_nonneg.mpr (hL.le.trans (hbulk (j, i)))
  rw [movingRegularSlot_card, Nat.mul_add, Nat.add_comm (2 ^ n * s)]
  calc
    _ ≤ (2 ^ (2 ^ n * m + 2 ^ n * s) * ((2 ^ n * m).factorial : ℝ) *
        ((2 ^ n * s).factorial : ℝ)) *
        ((L⁻¹) ^ (2 ^ n * m) * Real.exp (C * L * (2 ^ n * s : ℕ))) :=
      mul_le_mul hf hp hp0 (by positivity)
    _ = (2 ^ (2 ^ n * s) * ((2 ^ n * s).factorial : ℝ) *
        Real.exp (C * L * (2 ^ n * s : ℕ))) *
        (2 ^ (2 ^ n * m) * (((2 ^ n * m).factorial : ℝ) * (L⁻¹) ^ (2 ^ n * m))) := by
      rw [pow_add]
      ring
    _ ≤ (2 ^ (2 ^ n * s) * ((2 ^ n * s).factorial : ℝ) *
        Real.exp (C * L * (2 ^ n * s : ℕ))) *
        (2 ^ (2 ^ n * m) * Real.exp (Real.log ((2 ^ n : ℕ) * z) * (2 ^ n * m : ℕ))) := by
      gcongr
    _ = _ := by
      rw [Real.log_mul (by positivity : ((2 ^ n : ℕ) : ℝ) ≠ 0) hz.ne']
      have ht : (2 : ℝ) ^ (2 ^ n * m) = Real.exp ((2 ^ n * m : ℕ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      rw [ht, ← Real.exp_add]
      congr 2
      ring

end Ostmann

end OAI
