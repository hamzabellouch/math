import OAI.NumberTheory.Ostmann.Preliminaries.MertensPrimeBands
import OAI.NumberTheory.Ostmann.Preliminaries.TailCollisionCutoff

namespace OAI

/-! # Both logarithmic prime bands lie inside the collision cutoff -/

namespace Ostmann

open scoped Classical

theorem exp_prime_band_le_tail_cutoff (T L : ℝ) (hT : 4096 ≤ T)
    (hTL : T ^ (3 / 2 : ℝ) ≤ L) (hLU : L ≤ 2 * T ^ 2) :
    Real.exp (2 * T) ≤ Real.exp (L / 2) / L ^ 5 := by
  have hT1 : 1 ≤ T := by linarith
  have hTp : 0 < T := by linarith
  have hsqrt : (64 : ℝ) ≤ Real.sqrt T := by
    have hh := Real.sqrt_le_sqrt hT
    have he : Real.sqrt (4096 : ℝ) = 64 := by
      rw [show (4096 : ℝ) = 64 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    simpa only [he] using hh
  have hpow : 64 * T ≤ T ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hTp,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
    nlinarith
  have hLp : 0 < L := by linarith
  have hlog : Real.log L ≤ 2 + 2 * T := by
    have hh := Real.log_le_log hLp hLU
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hTp.ne'), Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    have htlog := Real.log_le_self hTp.le
    have h2log : Real.log (2 : ℝ) ≤ 2 := Real.log_le_self (by norm_num)
    linarith
  apply (Real.le_log_iff_exp_le (show 0 < Real.exp (L / 2) / L ^ 5 by positivity)).mp
  rw [Real.log_div (Real.exp_ne_zero _) (pow_ne_zero 5 hLp.ne'), Real.log_exp, Real.log_pow]
  linarith

theorem logPrimeBand_subset_tailCollisionCutoff (T L U : ℝ) (hT : 4096 ≤ T)
    (hTL : T ^ (3 / 2 : ℝ) ≤ L) (hLU : L ≤ 2 * T ^ 2) (hU : U ≤ T) :
    logPrimeBand U ⊆ Nat.primesLE (tailCollisionCutoff L) := by
  intro p hp
  have hpp := (logPrimeBand_mem hp).1
  apply Nat.mem_primesLE.mpr
  refine ⟨?_, hpp⟩
  have hpbound := Nat.le_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
  apply hpbound.trans
  apply Nat.floor_mono
  exact (Real.exp_le_exp.mpr (by linarith : 2 * U ≤ 2 * T)).trans
    (exp_prime_band_le_tail_cutoff T L hT hTL hLU)

end Ostmann

end OAI
