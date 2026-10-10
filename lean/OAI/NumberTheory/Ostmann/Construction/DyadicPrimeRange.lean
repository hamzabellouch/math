import Mathlib.Analysis.SpecialFunctions.Log.Base
import OAI.NumberTheory.Ostmann.Construction.HarmonicResidueDomination

namespace OAI

/-! # Concrete dyadic covers of the prime ranges used by the prior comparison -/

namespace Ostmann

/-- A lower endpoint at least twice the modulus ensures every dyadic
interval in the cover is long enough for the uniform residue bound. -/
theorem dyadic_prime_range_cover (A B q : ℕ) (hq : 0 < q) (hA : 2 * q ≤ A)
    (S : Finset ℕ) (hS : ∀ p ∈ S, A ≤ p ∧ p ≤ B) :
    q ≤ 2 ^ Nat.log 2 A ∧
      ∀ p ∈ S, 2 ^ Nat.log 2 A ≤ p ∧ p < 2 ^ (Nat.log 2 A + (Nat.log 2 B + 1)) := by
  have hA0 : A ≠ 0 := by omega
  have hbound := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) A
  have hqpow : q ≤ 2 ^ Nat.log 2 A := by
    rw [pow_succ] at hbound
    omega
  refine ⟨hqpow, fun p hp => ⟨(Nat.pow_log_le_self 2 hA0).trans (hS p hp).1, ?_⟩⟩
  have hB := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) B
  apply ((hS p hp).2.trans_lt hB).trans_le
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Even a doubly exponential prime endpoint needs only exponentially
many dyadic blocks. The constant is explicit and independent of the tree. -/
theorem dyadic_prime_range_count (B : ℕ) (C L : ℝ) (hC : 0 ≤ C) (hL : 1 ≤ L)
    (hB : (B : ℝ) ≤ Real.exp (Real.exp (C * L))) :
    ((Nat.log 2 B + 1 : ℕ) : ℝ) ≤
      Real.exp ((C + Real.log ((Real.log 2)⁻¹ + 1)) * L) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogB : Real.log B ≤ Real.exp (C * L) := by
    by_cases hB0 : B = 0
    · subst B
      simp only [Nat.cast_zero, Real.log_zero]
      exact (Real.exp_pos _).le
    · exact (Real.log_le_iff_le_exp (by exact_mod_cast Nat.pos_of_ne_zero hB0)).mpr hB
  have hnat : (Nat.log 2 B : ℝ) ≤ Real.log B / Real.log 2 := by
    simpa only [Real.logb, Nat.cast_ofNat] using Real.natLog_le_logb B 2
  have hexp1 : 1 ≤ Real.exp (C * L) := Real.one_le_exp (mul_nonneg hC (by linarith))
  have hconstant : 1 ≤ (Real.log 2)⁻¹ + 1 := by linarith [inv_pos.mpr hlog2]
  have hconstantpos : 0 < (Real.log 2)⁻¹ + 1 := lt_of_lt_of_le (by norm_num) hconstant
  have hlogconst : 0 ≤ Real.log ((Real.log 2)⁻¹ + 1) := Real.log_nonneg hconstant
  calc
    _ ≤ Real.log B / Real.log 2 + 1 := by push_cast; linarith
    _ ≤ Real.exp (C * L) / Real.log 2 + 1 := by gcongr
    _ ≤ ((Real.log 2)⁻¹ + 1) * Real.exp (C * L) := by
      rw [div_eq_mul_inv]
      nlinarith
    _ = Real.exp (Real.log ((Real.log 2)⁻¹ + 1) + C * L) := by
      rw [Real.exp_add, Real.exp_log hconstantpos]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith

end Ostmann

end OAI
