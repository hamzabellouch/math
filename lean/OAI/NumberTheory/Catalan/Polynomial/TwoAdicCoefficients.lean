import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import OAI.NumberTheory.Catalan.Determinants.RealColumnDeterminant

namespace OAI


noncomputable section

open Polynomial

namespace InternalCatalan

theorem chebyshev_T_coeff_two_pow_dvd (d : ℤ) (u : ℕ) :
    (2 : ℤ) ^ (u - 1) ∣ (Chebyshev.T ℤ d).coeff u := by
  cases u with
  | zero => simp
  | succ k =>
    simp only [Nat.succ_sub_one]
    refine ⟨(Chebyshev.C ℤ d).coeff (k + 1), ?_⟩
    have hc : (Chebyshev.C ℤ d).coeff (k + 1) * (2 : ℤ) ^ (k + 1) =
        2 * (Chebyshev.T ℤ d).coeff (k + 1) := by
      simpa only [← Polynomial.C_ofNat, comp_C_mul_X_coeff, coeff_C_mul] using
        congrArg (fun P : ℤ[X] => P.coeff (k + 1))
          (Chebyshev.C_comp_two_mul_X ℤ d)
    apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
    calc
      2 * (Chebyshev.T ℤ d).coeff (k + 1) =
          (Chebyshev.C ℤ d).coeff (k + 1) * 2 ^ (k + 1) := hc.symm
      _ = 2 * (2 ^ k * (Chebyshev.C ℤ d).coeff (k + 1)) := by ring

theorem chebyshev_U_coeff_two_pow_dvd (d : ℤ) (u : ℕ) :
    (2 : ℤ) ^ u ∣ (Chebyshev.U ℤ d).coeff u := by
  refine ⟨(Chebyshev.S ℤ d).coeff u, ?_⟩
  rw [← Chebyshev.S_comp_two_mul_X ℤ d]
  simp only [← Polynomial.C_ofNat, comp_C_mul_X_coeff]
  ring

theorem reversed_T_coeff_two_pow_dvd (C : ℕ) (d : ℤ) (i : ℕ) :
    (2 : ℤ) ^ (C - 1 - i - 1) ∣
      (reversedRow C (Chebyshev.T ℤ d)).coeff i := by
  rw [reversedRow_coeff]
  split_ifs
  · exact chebyshev_T_coeff_two_pow_dvd d (C - 1 - i)
  · exact dvd_zero _

theorem signed_reversed_U_coeff_two_pow_dvd (C : ℕ) (s d : ℤ) (i : ℕ) :
    (2 : ℤ) ^ (C - 1 - i) ∣
      (Polynomial.C s * reversedRow C (Chebyshev.U ℤ d)).coeff i := by
  rw [coeff_C_mul, reversedRow_coeff]
  split_ifs
  · exact dvd_mul_of_dvd_right (chebyshev_U_coeff_two_pow_dvd d (C - 1 - i)) s
  · simp

theorem le_two_adic_int_of_pow_dvd {z : ℤ} {u : ℕ}
    (hz : z ≠ 0) (hdiv : (2 : ℤ) ^ u ∣ z) : u ≤ padicValInt 2 z := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzabs : z.natAbs ≠ 0 := by simpa using hz
  have hdivabs : 2 ^ u ∣ z.natAbs := by
    simpa using (Int.natAbs_dvd_natAbs.mpr hdiv)
  exact (padicValNat_dvd_iff_le hzabs).mp hdivabs

theorem chebyshev_T_coeff_two_adic_le (d : ℤ) (u : ℕ)
    (hz : (Chebyshev.T ℤ d).coeff u ≠ 0) :
    (u : ℤ) - 1 ≤ padicValRat 2 ((Chebyshev.T ℤ d).coeff u : ℚ) := by
  have hv := le_two_adic_int_of_pow_dvd hz (chebyshev_T_coeff_two_pow_dvd d u)
  rw [padicValRat.of_int]
  omega

theorem chebyshev_U_coeff_two_adic_le (d : ℤ) (u : ℕ)
    (hz : (Chebyshev.U ℤ d).coeff u ≠ 0) :
    (u : ℤ) ≤ padicValRat 2 ((Chebyshev.U ℤ d).coeff u : ℚ) := by
  have hv := le_two_adic_int_of_pow_dvd hz (chebyshev_U_coeff_two_pow_dvd d u)
  rw [padicValRat.of_int]
  exact_mod_cast hv

end InternalCatalan

end

end OAI
