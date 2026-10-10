import OAI.NumberTheory.Ostmann.Preliminaries.HBootstrap

namespace OAI

namespace Ostmann.Preliminaries
open Filter

theorem eighth_power_refinement_algebra {q l A B C c w : ℝ}
    (hq : 0 < q) (hl : 0 < l) (hB : 0 < B) (hC : 0 < C) (hc : 0 < c)
    (hw : 0 ≤ w) (hlq : l ≤ q)
    (hprod : c * q ^ 8 / (8 * l) ≤ A * B)
    (hA : A ≤ 4 * C * q ^ 6 * l) :
    w * q / B ≤ (32 * C * w / c) * l := by
  have hmain := (div_le_iff₀ (show 0 < 8 * l by positivity)).mp
    (hprod.trans (mul_le_mul_of_nonneg_right hA hB.le))
  have hcore : c * q ^ 2 ≤ 32 * C * l ^ 2 * B := by
    apply (mul_le_mul_iff_left₀ (pow_pos hq 6)).mp
    nlinarith [hmain]
  have hmid : 32 * C * l ^ 2 * B ≤ 32 * C * l * q * B := by
    have h := mul_le_mul_of_nonneg_left hlq (show 0 ≤ 32 * C * l * B by positivity)
    nlinarith
  have hcancel : c * q ≤ 32 * C * l * B := by
    apply (mul_le_mul_iff_right₀ hq).mp
    nlinarith [hcore.trans hmid]
  apply (div_le_iff₀ hB).mpr
  apply (mul_le_mul_iff_left₀ hc).mp
  have h := mul_le_mul_of_nonneg_left hcancel hw
  field_simp
  nlinarith

theorem eventually_H_le_log_of_rough_count (d : Decomposition) {C : ℝ} (hC : 0 < C)
    (hrough : ∀ᶠ Q : ℕ in atTop,
      (countUpTo d.A (Q ^ 2) : ℝ) ≤ C * Q * Real.sqrt Q * Real.log Q) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Q : ℕ in atTop,
      residueReciprocalSum d.B Q ≤ K * Real.log Q := by
  let c : ℝ := Real.log 2 / 2
  let K : ℝ := 8 + 32 * C * Real.log 4 / c
  have hc : 0 < c := by dsimp [c]; positivity
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  have h4 : Tendsto (fun Q : ℕ => Q ^ 4) atTop atTop := tendsto_pow_atTop (by decide)
  have h8 : Tendsto (fun Q : ℕ => Q ^ 8) atTop atTop := tendsto_pow_atTop (by decide)
  have hBpos := (countUpTo_tendsto d.B d.infinite_B).eventually_ge_atTop 1
  filter_upwards [h4.eventually hrough, h8.eventually (eventually_count_product_lower d),
    h8.eventually hBpos, eventually_ge_atTop 2] with Q hA hprod hB hQ
  have hqr : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hl : 0 < Real.log (Q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hQ8 : 1 ≤ Q ^ 8 := one_le_pow₀ (by omega : 1 ≤ Q)
  have hBnat : 0 < countUpTo d.B (Q ^ 8) := by omega
  have hBreal : (0 : ℝ) < countUpTo d.B (Q ^ 8) := by exact_mod_cast hBnat
  have hlogs : Real.log ((Q ^ 8 : ℕ) : ℝ) = 8 * Real.log (Q : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hsqrt : Real.sqrt ((Q ^ 4 : ℕ) : ℝ) = (Q : ℝ) ^ 2 := by
    rw [Nat.cast_pow, show (Q : ℝ) ^ 4 = ((Q : ℝ) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg _)]
  have hA' : (countUpTo d.A (Q ^ 8) : ℝ) ≤ 4 * C * (Q : ℝ) ^ 6 * Real.log Q := by
    rw [← pow_mul] at hA
    norm_num only at hA
    rw [hsqrt, Nat.cast_pow, Real.log_pow] at hA
    norm_num only [Nat.cast_ofNat] at hA
    nlinarith [hA]
  have hprod' : c * (Q : ℝ) ^ 8 / (8 * Real.log Q) ≤
      (countUpTo d.A (Q ^ 8) : ℝ) * countUpTo d.B (Q ^ 8) := by
    simpa only [c, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using hprod
  have herror := eighth_power_refinement_algebra hqr hl hBreal hC hc hlog4
    ((Real.log_le_sub_one_of_pos hqr).trans (by linarith)) hprod' hA'
  have hH := residueReciprocalSum_le d.B Q (Q ^ 8) hQ8 hBnat
  rw [hlogs] at hH
  dsimp [K]
  linarith

theorem eventually_count_square_sharp_of_H (d : Decomposition) {C : ℝ} (hC : 0 < C)
    (hH : ∀ᶠ Q : ℕ in atTop, residueReciprocalSum d.B Q ≤ C * Real.log Q) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Q : ℕ in atTop,
      (countUpTo d.A (Q ^ 2) : ℝ) ≤ K * Q * Real.log (Q : ℝ) ^ 2 := by
  let K : ℝ := countSieveConstant * C + d.cutoff + 2
  have hK : 0 < K := by dsimp [K]; have := countSieveConstant_pos; positivity
  refine ⟨K, hK, ?_⟩
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  filter_upwards [eventually_count_square_le_H d, hH, hlog, eventually_ge_atTop 1] with Q hcount hH hlog hQ
  change 1 ≤ Real.log (Q : ℝ) at hlog
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hmult : 0 ≤ countSieveConstant * (Q : ℝ) * Real.log Q := by
    have := countSieveConstant_pos
    positivity
  have hh := mul_le_mul_of_nonneg_left hH hmult
  have hbase : (Q : ℝ) ≤ Q * Real.log (Q : ℝ) ^ 2 := by nlinarith [sq_nonneg (Real.log (Q : ℝ) - 1)]
  have hcut : (Q : ℝ) + d.cutoff + 1 ≤ ((d.cutoff : ℝ) + 2) * (Q * Real.log (Q : ℝ) ^ 2) := by
    have hn : (0 : ℝ) ≤ d.cutoff := by positivity
    nlinarith
  dsimp [K]
  nlinarith

end Ostmann.Preliminaries

end OAI
