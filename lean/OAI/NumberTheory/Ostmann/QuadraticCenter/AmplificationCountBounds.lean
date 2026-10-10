import OAI.NumberTheory.Ostmann.Construction.SmallPrimeSubset

namespace OAI

/-! # The precise number of small primes required for amplification -/

namespace Ostmann

private theorem original_scale_power_quotient (T : ℝ) (hT : 0 < T) :
    T / T ^ (1 / 10000000 : ℝ) = T ^ (9999999 / 10000000 : ℝ) := by
  rw [show (9999999 / 10000000 : ℝ) = 1 - 1 / 10000000 by norm_num,
    Real.rpow_sub hT, Real.rpow_one]

theorem amplificationPrimeCount_bounds (T : ℝ) (z : ℕ) (hT : 0 < T)
    (hlo : T ^ (1 / 10000000 : ℝ) / 2 ≤ Real.log (2 * (z : ℝ)))
    (hhi : Real.log (2 * (z : ℝ)) ≤ 8 * T ^ (1 / 10000000 : ℝ))
    (hlarge : 3000000 ≤ T ^ (9999999 / 10000000 : ℝ)) :
    3000 ≤ amplificationPrimeCount T z ∧
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (amplificationPrimeCount T z : ℝ) ∧
      (amplificationPrimeCount T z : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) := by
  let R := T ^ (9999999 / 10000000 : ℝ)
  let u := T ^ (1 / 10000000 : ℝ)
  let b := Real.log (2 * (z : ℝ))
  have hu : 0 < u := Real.rpow_pos_of_pos hT _
  have hb : 0 < b := lt_of_lt_of_le (by positivity) hlo
  have hratio : T / u = R := original_scale_power_quotient T hT
  have hrlo : R / 400 ≤ T / (50 * b) := by
    calc
      R / 400 = T / (400 * u) := by rw [← hratio]; ring
      _ ≤ T / (50 * b) := div_le_div_of_nonneg_left hT.le (by positivity) (by dsimp [b, u]; linarith)
  have hrhi : T / (50 * b) ≤ R / 25 := by
    calc
      T / (50 * b) ≤ T / (25 * u) := div_le_div_of_nonneg_left hT.le (by positivity) (by dsimp [b, u]; linarith)
      _ = R / 25 := by rw [← hratio]; ring
  have hfloorlo := Nat.sub_one_lt_floor (T / (50 * b))
  change T / (50 * b) - 1 < (amplificationPrimeCount T z : ℝ) at hfloorlo
  have hfloorhi : (amplificationPrimeCount T z : ℝ) ≤ T / (50 * b) :=
    Nat.floor_le (by positivity)
  have hR : 3000000 ≤ R := hlarge
  have hKlo : R / 1000 ≤ (amplificationPrimeCount T z : ℝ) := by linarith
  refine ⟨?_, hKlo, ?_⟩
  · have hh : (3000 : ℝ) ≤ (amplificationPrimeCount T z : ℝ) := by linarith
    exact_mod_cast hh
  · linarith

end Ostmann

end OAI
