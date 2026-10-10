import OAI.NumberTheory.EgyptianFractions.RandomProductParameters

namespace OAI
noncomputable section

open Filter
open scoped Topology

namespace Problem337.RandomProducts

/-- `floor(S/log S)` eventually exceeds every fixed multiple of `log S`. -/
theorem eventually_blockLength_ge_log_mul (C : ℝ) :
    ∀ᶠ S : ℝ in atTop, C * Real.log S ≤ (blockLength S : ℝ) := by
  have hlim : Tendsto (fun S : ℝ => (C + 1) * Real.log S ^ 2 / S)
      atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := C + 1)).mul
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 (by norm_num))
    simpa only [one_mul, add_zero, mul_zero, mul_div_assoc] using h
  filter_upwards [hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
      eventually_gt_atTop (0 : ℝ)] with S hsmall hlog hS
  have hlogpos : 0 < Real.log S := by linarith
  have hbound := (div_lt_iff₀ hS).mp hsmall
  have hdiv : C * Real.log S + 1 ≤ S / Real.log S := by
    apply (le_div_iff₀ hlogpos).mpr
    nlinarith
  have hfloor := Nat.sub_one_lt_floor (S / Real.log S)
  dsimp [blockLength]
  linarith

theorem tendsto_blockLength_div_log_atTop :
    Tendsto (fun S : ℝ => (blockLength S : ℝ) / Real.log S) atTop atTop := by
  apply tendsto_atTop.mpr
  intro C
  filter_upwards [eventually_blockLength_ge_log_mul C,
    eventually_gt_atTop (1 : ℝ)] with S hS hSone
  exact (le_div_iff₀ (Real.log_pos hSone)).mpr hS

theorem tendsto_blockLength_real_atTop :
    Tendsto (fun S : ℝ => (blockLength S : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ Real.tendsto_log_atTop
  filter_upwards [eventually_blockLength_ge_log_mul 1] with S hS
  simpa only [one_mul] using hS

/-- The union over `O(log S)` middle levels has vanishing failure mass. -/
theorem tendsto_middle_failure_zero (K : ℝ) (hK : 0 ≤ K) :
    Tendsto (fun S : ℝ => K * Real.log S * Real.exp (-(blockLength S : ℝ) / 250))
      atTop (𝓝 0) := by
  have hKlim : Tendsto (fun S : ℝ => K / S) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply squeeze_zero' ?_ ?_ hKlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with S hS
    exact mul_nonneg (mul_nonneg hK (Real.log_nonneg hS)) (Real.exp_pos _).le
  · filter_upwards [eventually_blockLength_ge_log_mul 500,
      eventually_gt_atTop (1 : ℝ)] with S hbound hS
    have hSpos : 0 < S := by linarith
    have hlog : 0 ≤ Real.log S := (Real.log_pos hS).le
    have hlogle : Real.log S ≤ S := by
      have := Real.log_le_sub_one_of_pos hSpos
      linarith
    have hexp : Real.exp (-(blockLength S : ℝ) / 250) ≤ 1 / S ^ 2 := by
      calc
        Real.exp (-(blockLength S : ℝ) / 250) ≤ Real.exp (-2 * Real.log S) :=
          Real.exp_le_exp.mpr (by linarith)
        _ = 1 / S ^ 2 := by
          rw [show -2 * Real.log S = -Real.log (S ^ 2) by rw [Real.log_pow]; norm_num,
            Real.exp_neg, Real.exp_log (by positivity)]
          simp [one_div]
    calc
      K * Real.log S * Real.exp (-(blockLength S : ℝ) / 250) ≤
          K * S * (1 / S ^ 2) := by gcongr
      _ = K / S := by field_simp

/-- Uniform lower cutoff for all middle-level numerators. -/
theorem eventually_middle_lower_cutoff :
    ∀ᶠ S : ℝ in atTop, ∀ V : ℝ,
      (9999 / 10000 : ℝ) * (blockLength S : ℝ) ≤ V →
      100000 * Real.log S ≤ V := by
  filter_upwards [eventually_blockLength_ge_log_mul 200000,
    eventually_ge_atTop (1 : ℝ)] with S hblock hS V hV
  have hlog := Real.log_nonneg hS
  have hm : (0 : ℝ) ≤ blockLength S := Nat.cast_nonneg _
  nlinarith

/-- Frequencies used by the middle-level discrepancy test lie within the
range covered by the random second moment. -/
theorem middle_frequency_cutoff {m V : ℝ} (hm : 0 ≤ m)
    (hV : (9999 / 10000 : ℝ) * m ≤ V) :
    Real.exp (m / 2500) ≤ Real.exp (min m V / 200) := by
  apply Real.exp_le_exp.mpr
  have hmin : (9999 / 10000 : ℝ) * m ≤ min m V :=
    le_min (by nlinarith) hV
  linarith

/-- One frequency union bound and Markov's inequality at the middle levels. -/
theorem middle_fourier_failure_bound {m w : ℝ} (hm : 0 ≤ m)
    (hw : (9999 / 10000 : ℝ) * m ≤ w) :
    Real.exp (m / 2500) * Real.exp (3 * m / 5000) * Real.exp (-w / 100) ≤
      Real.exp (-m / 200) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- The second Markov step has exactly the exponent used in the level union. -/
theorem middle_second_markov_factor (m : ℝ) :
    Real.exp (-m / 200) / Real.exp (-m / 1000) = Real.exp (-m / 250) := by
  rw [← Real.exp_sub]
  congr 1
  ring

/-- The corresponding first-block bound for terminal numerators. -/
theorem terminal_fourier_failure_bound {V : ℝ} (hV : 0 ≤ V) :
    Real.exp (V / 2500) * Real.exp (3 * V / 5000) * Real.exp (-V / 100) ≤
      Real.exp (-V / 200) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- Independence of 1000 terminal blocks converts the single-block estimate
into a summable fifth-power tail. -/
theorem terminal_thousand_blocks_bound {V p : ℝ} (hp : 0 ≤ p)
    (hbound : p ≤ Real.exp (-V / 200)) :
    p ^ 1000 ≤ Real.exp (-5 * V) := by
  calc
    p ^ 1000 ≤ Real.exp (-V / 200) ^ 1000 := pow_le_pow_left₀ hp hbound _
    _ = Real.exp (-5 * V) := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      ring

end Problem337.RandomProducts

end

end OAI
