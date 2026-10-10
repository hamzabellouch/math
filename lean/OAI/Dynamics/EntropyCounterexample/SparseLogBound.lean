import Mathlib

namespace OAI

noncomputable section

open Filter Topology

namespace Problem340.SparseLogBound

def rate (m P Q τ J : ℝ) (r : ℕ) : ℝ :=
  Real.log ((2 : ℝ) ^ r * P ^ r * Q ^ ⌈τ * (r : ℝ) + J⌉₊) /
    (m * (r : ℝ))

def principalRate (m P Q τ : ℝ) : ℝ :=
  (Real.log 2 + Real.log P + τ * Real.log Q) / m

lemma log_code_count (P Q τ J : ℝ) (hP : 0 < P) (hQ : 0 < Q) (r : ℕ) :
    Real.log ((2 : ℝ) ^ r * P ^ r * Q ^ ⌈τ * (r : ℝ) + J⌉₊) =
      (r : ℝ) * Real.log 2 + (r : ℝ) * Real.log P +
        (⌈τ * (r : ℝ) + J⌉₊ : ℝ) * Real.log Q := by
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]

theorem rate_le (m P Q τ J : ℝ) (hm : 0 < m)
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hτ : 0 ≤ τ) (hJ : 0 ≤ J)
    {r : ℕ} (hr : 0 < r) :
    rate m P Q τ J r ≤ principalRate m P Q τ +
      ((J + 1) * Real.log Q) / (m * (r : ℝ)) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hceil : (⌈τ * (r : ℝ) + J⌉₊ : ℝ) ≤ τ * (r : ℝ) + J + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  rw [rate, log_code_count P Q τ J (by linarith) (by linarith)]
  calc
    _ ≤ ((r : ℝ) * Real.log 2 + (r : ℝ) * Real.log P +
        (τ * (r : ℝ) + J + 1) * Real.log Q) / (m * (r : ℝ)) := by
      apply div_le_div_of_nonneg_right _ (mul_pos hm hr').le
      exact add_le_add_right (mul_le_mul_of_nonneg_right hceil hlogQ) _
    _ = principalRate m P Q τ + ((J + 1) * Real.log Q) / (m * (r : ℝ)) := by
      unfold principalRate
      field_simp
      ring

theorem principalRate_le_rate (m P Q τ J : ℝ) (hm : 0 < m)
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hJ : 0 ≤ J)
    {r : ℕ} (hr : 0 < r) :
    principalRate m P Q τ ≤ rate m P Q τ J r := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hceil : τ * (r : ℝ) ≤ (⌈τ * (r : ℝ) + J⌉₊ : ℝ) := by
    exact (le_add_of_nonneg_right hJ).trans (Nat.le_ceil _)
  rw [rate, log_code_count P Q τ J (by linarith) (by linarith)]
  calc
    principalRate m P Q τ =
      ((r : ℝ) * Real.log 2 + (r : ℝ) * Real.log P +
        (τ * (r : ℝ)) * Real.log Q) / (m * (r : ℝ)) := by
      unfold principalRate
      field_simp
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (mul_pos hm hr').le
      exact add_le_add_right
        (mul_le_mul_of_nonneg_right hceil (Real.log_nonneg hQ)) _

theorem tendsto_rate (m P Q τ J : ℝ) (hm : 0 < m)
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hτ : 0 ≤ τ) (hJ : 0 ≤ J) :
    Tendsto (rate m P Q τ J) atTop (𝓝 (principalRate m P Q τ)) := by
  have herr : Tendsto
      (fun r : ℕ => ((J + 1) * Real.log Q) / (m * (r : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Tendsto.const_mul_atTop hm tendsto_natCast_atTop_atTop)
  have hupp : Tendsto
      (fun r : ℕ => principalRate m P Q τ +
        ((J + 1) * Real.log Q) / (m * (r : ℝ)))
      atTop (𝓝 (principalRate m P Q τ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add herr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupp
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with r hr
    exact principalRate_le_rate m P Q τ J hm hP hQ hJ hr
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with r hr
    exact rate_le m P Q τ J hm hP hQ hτ hJ hr

theorem eventually_rate_lt (m P Q τ J : ℝ) (hm : 0 < m)
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hτ : 0 ≤ τ) (hJ : 0 ≤ J)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop,
      rate m P Q τ J r < principalRate m P Q τ + ε :=
  (tendsto_rate m P Q τ J hm hP hQ hτ hJ).eventually_lt_const (by linarith)

theorem eventually_nat_log_rate_lt
    (m P Q J : ℕ) (τ : ℝ) (hm : 0 < m) (hP : 1 ≤ P) (hQ : 1 ≤ Q)
    (hτ : 0 ≤ τ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop,
      Real.log ((2 ^ r * P ^ r * Q ^ ⌈τ * (r : ℝ) + (J : ℝ)⌉₊ : ℕ) : ℝ) /
          ((m * r : ℕ) : ℝ) <
        (Real.log 2 + Real.log (P : ℝ) + τ * Real.log (Q : ℝ)) / (m : ℝ) + ε := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hP' : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hQ' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  simpa only [rate, principalRate, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
    eventually_rate_lt (m : ℝ) P Q τ J hm' hP' hQ' hτ (Nat.cast_nonneg J) hε

end Problem340.SparseLogBound

end

end OAI
