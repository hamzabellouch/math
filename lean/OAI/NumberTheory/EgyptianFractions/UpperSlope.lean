import Mathlib

namespace OAI
open Filter
open scoped Topology

namespace Problem337

/-- A double logarithm estimate for the elementary denominator bound. -/
theorem loglog_le_of_power_bound {k : ℕ} {x : ℝ} (hk : 2 ≤ k)
    (hx : 2 ≤ x) (hbound : x ≤ 1 + (k : ℝ) ^ (2 ^ (k - 1))) :
    Real.log (Real.log x) ≤ (k : ℝ) * Real.log 2 + Real.log (Real.log k) := by
  have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : 0 < (k : ℝ) := by linarith
  have hkone : 1 ≤ (k : ℝ) := by linarith
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
  have hp : 1 ≤ (2 : ℕ) ^ (k - 1) := Nat.one_le_pow _ _ (by decide)
  have hpow : 2 ≤ (k : ℝ) ^ (2 ^ (k - 1)) := by
    calc
      2 ≤ (k : ℝ) := hkR
      _ = (k : ℝ) ^ 1 := by simp
      _ ≤ (k : ℝ) ^ (2 ^ (k - 1)) := pow_le_pow_right₀ hkone hp
  have hexp : (2 : ℕ) ^ (k - 1) * 2 = 2 ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hbound' : x ≤ (k : ℝ) ^ (2 ^ k) := by
    calc
      x ≤ 1 + (k : ℝ) ^ (2 ^ (k - 1)) := hbound
      _ ≤ ((k : ℝ) ^ (2 ^ (k - 1))) ^ 2 := by nlinarith
      _ = (k : ℝ) ^ (2 ^ k) := by rw [← pow_mul, hexp]
  have hlog : Real.log x ≤ (2 : ℝ) ^ k * Real.log (k : ℝ) := by
    simpa only [Real.log_pow, Nat.cast_pow, Nat.cast_ofNat] using
      Real.log_le_log (by linarith : 0 < x) hbound'
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  calc
    Real.log (Real.log x) ≤ Real.log ((2 : ℝ) ^ k * Real.log (k : ℝ)) :=
      Real.log_le_log hlogx hlog
    _ = (k : ℝ) * Real.log 2 + Real.log (Real.log k) := by
      rw [Real.log_mul (by positivity) (ne_of_gt hlogk), Real.log_pow]

/-- The logarithmic error in the denominator upper bound is negligible. -/
theorem tendsto_log_nat_div_nat :
    Tendsto (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ)) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  simpa [Function.comp_def] using h.comp tendsto_natCast_atTop_atTop

/-- The elementary power upper bound forces the sharp upper logarithmic slope. -/
theorem power_bound_slope_limits (u : ℕ → ℝ)
    (hu : ∀ᶠ k in atTop, 2 ≤ u k ∧
      u k ≤ 1 + (k : ℝ) ^ (2 ^ (k - 1))) :
    0 ≤ liminf (fun k => Real.log (Real.log (u k)) / (k : ℝ)) atTop ∧
    liminf (fun k => Real.log (Real.log (u k)) / (k : ℝ)) atTop ≤
      limsup (fun k => Real.log (Real.log (u k)) / (k : ℝ)) atTop ∧
    limsup (fun k => Real.log (Real.log (u k)) / (k : ℝ)) atTop ≤ Real.log 2 := by
  let f : ℕ → ℝ := fun k => Real.log (Real.log (u k)) / (k : ℝ)
  have hupp : f ≤ᶠ[atTop] (fun k : ℕ => Real.log 2 + Real.log (k : ℝ) / (k : ℝ)) := by
    filter_upwards [hu, eventually_ge_atTop 2] with k hk hk2
    have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk2
    have hkpos : 0 < (k : ℝ) := by linarith
    have hlog : Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ) := by
      apply Real.log_le_log (Real.log_pos (by linarith))
      linarith [Real.log_le_sub_one_of_pos hkpos]
    have hmain := loglog_le_of_power_bound hk2 hk.1 hk.2
    calc
      f k ≤ ((k : ℝ) * Real.log 2 + Real.log (k : ℝ)) / (k : ℝ) := by
        apply div_le_div_of_nonneg_right _ hkpos.le
        exact hmain.trans (add_le_add (le_refl _) hlog)
      _ = Real.log 2 + Real.log (k : ℝ) / (k : ℝ) := by
        field_simp
  have hlo : (fun k : ℕ => Real.log (Real.log 2) / (k : ℝ)) ≤ᶠ[atTop] f := by
    filter_upwards [hu, eventually_ge_atTop 2] with k hk hk2
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
    exact Real.log_le_log (Real.log_pos (by norm_num))
      (Real.log_le_log (by norm_num) hk.1)
  have htU : Tendsto (fun k : ℕ => Real.log 2 + Real.log (k : ℝ) / (k : ℝ))
      atTop (𝓝 (Real.log 2)) := by
    simpa using tendsto_const_nhds.add tendsto_log_nat_div_nat
  have htL : Tendsto (fun k : ℕ => Real.log (Real.log 2) / (k : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hfbU : atTop.IsBoundedUnder (· ≤ ·) f := htU.isBoundedUnder_le.mono_le hupp
  have hfbL : atTop.IsBoundedUnder (· ≥ ·) f := htL.isBoundedUnder_ge.mono_ge hlo
  change 0 ≤ liminf f atTop ∧ liminf f atTop ≤ limsup f atTop ∧
    limsup f atTop ≤ Real.log 2
  refine ⟨?_, liminf_le_limsup hfbU hfbL, ?_⟩
  · calc
      0 = liminf (fun k : ℕ => Real.log (Real.log 2) / (k : ℝ)) atTop := htL.liminf_eq.symm
      _ ≤ liminf f atTop := liminf_le_liminf hlo htL.isBoundedUnder_ge hfbU.isCobounded_flip
  · calc
      limsup f atTop ≤ limsup (fun k : ℕ => Real.log 2 + Real.log (k : ℝ) / (k : ℝ)) atTop :=
        limsup_le_limsup hupp hfbL.isCobounded_flip htU.isBoundedUnder_le
      _ = Real.log 2 := htU.limsup_eq

end Problem337

end OAI
