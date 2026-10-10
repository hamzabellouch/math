import OAI.NumberTheory.Ostmann.Construction.DyadicPrimeSelection
import OAI.NumberTheory.Ostmann.Construction.DyadicShellBudget

namespace OAI

/-! # Weighted biased primes give a block of the required population size -/

namespace Ostmann

open scoped BigOperators Classical

theorem exists_populated_prime_block (P : Finset ℕ) (M : ℕ) (T d : ℝ)
    (hT : 1 ≤ T) (hd : 0 < d) (hP : ∀ p ∈ P, p.Prime)
    (hM : ∀ p ∈ P, p ≤ M) (hMexp : (M : ℝ) ≤ Real.exp (2 * T))
    (hmass : d * T ≤ ∑ p ∈ P, Real.log (p : ℝ) / p) :
    ∃ (Z : ℕ) (R : Finset ℕ), 2 ≤ Z ∧ R ⊆ P ∧ R.Nonempty ∧
      (∀ p ∈ R, Z ≤ p ∧ p < 2 * Z) ∧
      (Z : ℝ) ≤ ((4 + 4 / Real.log 2) / d) * Real.log Z * R.card := by
  have hTp : 0 < T := by linarith
  obtain ⟨Z, R, hZ, hRP, hR, hrange, hb⟩ := exists_weighted_dyadic_prime_block P M (d * T)
    hP hM (mul_pos hd hTp) hmass
  have hZ2 : 2 ≤ Z := by
    obtain ⟨p, hp⟩ := hR
    have := (hP p (hRP hp)).two_le
    have := (hrange p hp).2
    omega
  have hZR : (0 : ℝ) < Z := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hZ2)
  have hlogZ : 0 ≤ Real.log (Z : ℝ) := Real.log_nonneg (by exact_mod_cast hZ)
  have hlog2 : Real.log 2 ≤ Real.log (Z : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hZ2)
  have hlog : Real.log (2 * (Z : ℝ)) ≤ 2 * Real.log Z := by
    rw [Real.log_mul (by norm_num) hZR.ne']
    linarith
  have hK := dyadic_shell_count_bound 2 T (by norm_num) hT M hMexp
  have hD : 0 ≤ 2 + 2 / Real.log 2 := by positivity
  have hupper : (Nat.log 2 M + 1 : ℝ) * Real.log (2 * (Z : ℝ)) * R.card ≤
      ((2 + 2 / Real.log 2) * T) * (2 * Real.log Z) * R.card := by
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    have hZ1 : (1 : ℝ) ≤ Z := by exact_mod_cast hZ
    exact mul_le_mul hK hlog (Real.log_nonneg (by linarith)) (mul_nonneg hD hTp.le)
  have hcancel : d * (Z : ℝ) ≤ (4 + 4 / Real.log 2) * Real.log Z * R.card := by
    apply (mul_le_mul_iff_right₀ hTp).mp
    convert hb.trans hupper using 1 <;> ring
  refine ⟨Z, R, hZ2, hRP, hR, hrange, ?_⟩
  have hh : (Z : ℝ) ≤ ((4 + 4 / Real.log 2) * Real.log Z * R.card) / d :=
    (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hcancel)
  convert hh using 1
  ring

end Ostmann

end OAI
