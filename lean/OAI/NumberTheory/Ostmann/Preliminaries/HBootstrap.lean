import OAI.NumberTheory.Ostmann.Preliminaries.CountSquare

namespace OAI

namespace Ostmann.Preliminaries
open Filter

theorem eventually_H_le_sqrt_of_polylog_lower (S : Set ℕ) (hS : S.Infinite)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ᶠ Y : ℕ in atTop, c * Real.log (Y : ℝ) ^ 2 ≤ countUpTo S Y) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Q : ℕ in atTop,
      residueReciprocalSum S Q ≤ C * Real.sqrt Q := by
  let C : ℝ := Real.sqrt (2 / c) + Real.log 4
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [(nthElement_tendsto S hS).eventually hlower, eventually_ge_atTop 1] with Q hlow hQ
  let Y := nthElement S Q
  have hQY : Q ≤ Y := nthElement_ge S hS Q
  have hY : 1 ≤ Y := hQ.trans hQY
  have hcount : countUpTo S Y = Q + 1 := countUpTo_nthElement S hS Q
  have hcountpos : 0 < countUpTo S Y := by omega
  have hupper := residueReciprocalSum_le S Q Y hY hcountpos
  rw [hcount, Nat.cast_add, Nat.cast_one] at hupper
  change c * Real.log (Y : ℝ) ^ 2 ≤ _ at hlow
  rw [hcount, Nat.cast_add, Nat.cast_one] at hlow
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQnonneg : (0 : ℝ) ≤ Q := by positivity
  have hsQ : 1 ≤ Real.sqrt (Q : ℝ) := Real.one_le_sqrt.mpr hQr
  have hsQsq := Real.sq_sqrt hQnonneg
  have hscsq := Real.sq_sqrt (show 0 ≤ 2 / c by positivity)
  have hlogY : Real.log (Y : ℝ) ≤ Real.sqrt (2 / c) * Real.sqrt Q := by
    have hratio : (2 / c) * c = 2 := by field_simp
    have hmul : (Real.sqrt (2 / c) * Real.sqrt Q) ^ 2 = (2 / c) * Q := by
      rw [mul_pow, hscsq, hsQsq]
    have hnonneg : 0 ≤ Real.sqrt (2 / c) * Real.sqrt Q := by positivity
    nlinarith
  have herror : Real.log 4 * (Q : ℝ) / ((Q : ℝ) + 1) ≤ Real.log 4 := by
    apply (div_le_iff₀ (by positivity : 0 < (Q : ℝ) + 1)).mpr
    nlinarith
  have hfinal : Real.log 4 ≤ Real.log 4 * Real.sqrt Q := by nlinarith
  dsimp [C]
  nlinarith

theorem eventually_count_square_rough (d : Decomposition) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ᶠ Y : ℕ in atTop, c * Real.log (Y : ℝ) ^ 2 ≤ countUpTo d.B Y) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Q : ℕ in atTop,
      (countUpTo d.A (Q ^ 2) : ℝ) ≤ C * Q * Real.sqrt Q * Real.log Q := by
  obtain ⟨C, hC, hH⟩ := eventually_H_le_sqrt_of_polylog_lower d.B d.infinite_B hc hlower
  let K : ℝ := countSieveConstant * C + d.cutoff + 2
  have hK : 0 < K := by dsimp [K]; have := countSieveConstant_pos; positivity
  refine ⟨K, hK, ?_⟩
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  filter_upwards [eventually_count_square_le_H d, hH, hlog, eventually_ge_atTop 1] with Q hcount hH hlog hQ
  change 1 ≤ Real.log (Q : ℝ) at hlog
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hs : 1 ≤ Real.sqrt (Q : ℝ) := Real.one_le_sqrt.mpr hQr
  have hmult : 0 ≤ countSieveConstant * (Q : ℝ) * Real.log Q := by
    have := countSieveConstant_pos
    positivity
  have hh := mul_le_mul_of_nonneg_left hH hmult
  have hbase : (Q : ℝ) ≤ (Q : ℝ) * Real.sqrt Q * Real.log Q := by
    calc
      (Q : ℝ) ≤ Q * Real.sqrt Q := by nlinarith
      _ ≤ Q * Real.sqrt Q * Real.log Q := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog
          (show 0 ≤ (Q : ℝ) * Real.sqrt Q by positivity)
  have hcut : (Q : ℝ) + d.cutoff + 1 ≤
      ((d.cutoff : ℝ) + 2) * (Q * Real.sqrt Q * Real.log Q) := by
    have hn : (0 : ℝ) ≤ d.cutoff := by positivity
    nlinarith
  dsimp [K]
  nlinarith

end Ostmann.Preliminaries

end OAI
