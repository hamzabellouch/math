import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import OAI.NumberTheory.Catalan.Estimates.RealHadamard
import OAI.NumberTheory.Catalan.Estimates.RealProjectiveVandermonde

namespace OAI

noncomputable section
open scoped BigOperators

namespace InternalCatalan

theorem weighted_real_vandermonde_le_sqrt {m : ℕ} (z : Fin m → ℝ) :
    |∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (z j - z i)| ≤
      (Real.sqrt (m : ℝ)) ^ m / (2 : ℝ) ^ (m.choose 2) *
        (∏ i : Fin m, Real.sqrt (1 + z i ^ 2) ^ (m - 1)) := by
  have hh := norm_det_le_of_entry_norm_eq
    (Matrix.projVandermonde
      (fun i => (z i : ℂ) + Complex.I) (fun i => (z i : ℂ) - Complex.I))
    (fun i => Real.sqrt (1 + z i ^ 2) ^ (m - 1))
    (fun i => pow_nonneg (Real.sqrt_nonneg _) _)
    (real_projectiveVandermonde_entry_norm z)
  rw [real_projectiveVandermonde_det_norm] at hh
  have hd : 0 < (2 : ℝ) ^ (m.choose 2) := by positivity
  calc
    _ ≤ ((Real.sqrt (m : ℝ)) ^ m *
        (∏ i : Fin m, Real.sqrt (1 + z i ^ 2) ^ (m - 1))) /
          (2 : ℝ) ^ (m.choose 2) := by
      apply (le_div_iff₀ hd).mpr
      simpa only [mul_comm] using hh
    _ = _ := by ring

private theorem sqrt_pow_eq_rpow_half {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    Real.sqrt x ^ k = x ^ ((k : ℝ) / 2) := by
  symm
  simpa only [Real.rpow_natCast] using Real.rpow_div_two_eq_sqrt (k : ℝ) hx

theorem weighted_real_vandermonde_le {m : ℕ} (hm : 0 < m) (z : Fin m → ℝ) :
    |∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (z j - z i)| ≤
      (m : ℝ) ^ ((m : ℝ) / 2) / (2 : ℝ) ^ (m.choose 2) *
        (∏ i : Fin m, (1 + z i ^ 2) ^ (((m : ℝ) - 1) / 2)) := by
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_one]
  have hhead := sqrt_pow_eq_rpow_half (Nat.cast_nonneg m : (0 : ℝ) ≤ m) m
  have hrow (i : Fin m) := sqrt_pow_eq_rpow_half
    (by positivity : (0 : ℝ) ≤ 1 + z i ^ 2) (m - 1)
  simpa only [hhead, hrow, hcast] using weighted_real_vandermonde_le_sqrt z

end InternalCatalan

end

end OAI
