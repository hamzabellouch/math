import OAI.Combinatorics.ProgressionColoring.ProbabilityScales
import OAI.Combinatorics.ProgressionColoring.PrimeScale

namespace OAI

noncomputable section

namespace QuantitativeVanDerWaerden.Parameters

theorem ceil_four_hundred_ge (k : ℕ) :
    (k : ℝ) / 400 ≤ ((k + 399) / 400 : ℕ) := by
  have hh : k ≤ 400 * ((k + 399) / 400) := by omega
  have hr : (k : ℝ) ≤ 400 * (((k + 399) / 400 : ℕ) : ℝ) := by exact_mod_cast hh
  linarith

theorem ceil_four_ge (k : ℕ) :
    (k : ℝ) / 4 ≤ ((k + 3) / 4 : ℕ) := by
  have hh : k ≤ 4 * ((k + 3) / 4) := by omega
  have hr : (k : ℝ) ≤ 4 * (((k + 3) / 4 : ℕ) : ℝ) := by exact_mod_cast hh
  linarith

theorem flipProbability_le_one {k : ℕ} (hk : 1 ≤ k) : flipProbability k ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hk) (by norm_num)

theorem flip_integer_power_le {k : ℕ} (hk : 1 ≤ k) :
    flipProbability k ^ ((k + 399) / 400) ≤
      flipProbability k ^ ((k : ℝ) / 400) := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge (flipProbability_pos (by omega))
    (flipProbability_le_one hk) (ceil_four_hundred_ge k)

theorem survival_integer_power_le {k : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) ^ ((k + 3) / 4) ≤ Real.exp (-(p * k) / 4) := by
  have he : 1 - p ≤ Real.exp (-p) := by
    have := Real.add_one_le_exp (-p)
    linarith
  calc
    (1 - p) ^ ((k + 3) / 4) ≤ Real.exp (-p) ^ ((k + 3) / 4) :=
      pow_le_pow_left₀ (by linarith) he _
    _ = Real.exp ((((k + 3) / 4 : ℕ) : ℝ) * (-p)) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (-(p * k) / 4) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left (ceil_four_ge k) hp
      nlinarith

theorem real_rich_risk_le {k q : ℕ} (hk : 2 ≤ k) (hq : 0 < q)
    (hlogq : (dimension k : ℝ) * Real.log q ≤
      c * k * Real.log k + (dimension k : ℝ) * Real.log (2 * (k : ℝ) ^ 2)) :
    2 * (q : ℝ) ^ (2 * dimension k) *
        flipProbability k ^ ((k : ℝ) / 400) ≤ richEnvelope k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hp := flipProbability_pos (by omega : 0 < k)
  have hqpow : (0 : ℝ) < (q : ℝ) ^ (2 * dimension k) := by positivity
  have hppow : 0 < flipProbability k ^ ((k : ℝ) / 400) :=
    Real.rpow_pos_of_pos hp _
  calc
    _ = Real.exp (Real.log (2 * (q : ℝ) ^ (2 * dimension k) *
        flipProbability k ^ ((k : ℝ) / 400))) :=
      (Real.exp_log (by positivity)).symm
    _ ≤ richEnvelope k := by
      apply Real.exp_le_exp.mpr
      rw [Real.log_mul (by positivity) hppow.ne',
        Real.log_mul (by norm_num) hqpow.ne', Real.log_pow, Real.log_rpow hp]
      rw [flipProbability, Real.log_rpow hk0]
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      change _ ≤ -(21 / 200000 : ℝ) * k * Real.log k +
        2 * dimension k * Real.log (2 * (k : ℝ) ^ 2) + Real.log 2
      dsimp [c] at hlogq
      nlinarith

theorem integer_rich_risk_le {k q : ℕ} (hk : 2 ≤ k) (hq : 0 < q)
    (hlogq : (dimension k : ℝ) * Real.log q ≤
      c * k * Real.log k + (dimension k : ℝ) * Real.log (2 * (k : ℝ) ^ 2)) :
    2 * (q : ℝ) ^ (2 * dimension k) *
        flipProbability k ^ ((k + 399) / 400) ≤ richEnvelope k := by
  exact (mul_le_mul_of_nonneg_left (flip_integer_power_le (by omega : 1 ≤ k))
    (by positivity)).trans (real_rich_risk_le hk hq hlogq)

theorem primeScale_rich_risk_le {k : ℕ} (hk : 2 ≤ k)
    (s : PrimeScale k (dimension k)) :
    2 * (s.q : ℝ) ^ (2 * dimension k) *
        flipProbability k ^ ((k + 399) / 400) ≤ richEnvelope k := by
  have hD : 1 ≤ dimension k := dimension_pos (by omega)
  exact integer_rich_risk_le hk s.pos (s.log_upper hk hD)

theorem integer_affine_risk_le {k : ℕ} (hk : 2 ≤ k) {C T : ℝ}
    (hT : 0 < T)
    (hentropy : Real.log T ≤ C * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log k) :
    2 * T * (1 - flipProbability k) ^ ((k + 3) / 4) ≤ affineEnvelope C k := by
  have hp := flipProbability_pos (by omega : 0 < k)
  exact (mul_le_mul_of_nonneg_left
    (survival_integer_power_le hp.le (flipProbability_le_one (by omega : 1 ≤ k)))
    (by positivity)).trans (affine_risk_le hk hT hentropy)

end QuantitativeVanDerWaerden.Parameters

end

end OAI
