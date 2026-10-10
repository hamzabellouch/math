import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.Construction.TailEndpointTests
import OAI.NumberTheory.Ostmann.Preliminaries.TailCollisionCutoff

namespace OAI

/-! # The cutoff used to test all large endpoint subsets -/

namespace Ostmann

open Filter

noncomputable def endpointTestCutoff (t : ℝ) : ℕ := ⌊Real.exp (t / 2) / t ^ 12⌋₊

noncomputable def endpointTestThreshold (t : ℝ) : ℕ := ⌈Real.exp (t / 2) / t ^ 10⌉₊

theorem endpointTestCutoff_bounds (t : ℝ) (ht : 1 ≤ t)
    (hr : 2 ≤ Real.exp (t / 2) / t ^ 12) :
    1 ≤ endpointTestCutoff t ∧
      (endpointTestCutoff t : ℝ) ≤ Real.exp (t / 2) / t ^ 12 ∧
      t / 2 - 12 * Real.log t - Real.log 2 ≤ Real.log (endpointTestCutoff t : ℝ) := by
  have htp : 0 < t := by linarith
  have hrp : 0 < Real.exp (t / 2) / t ^ 12 := by positivity
  have hQ : 1 ≤ endpointTestCutoff t := (Nat.one_le_floor_iff _).mpr (by linarith)
  have hhalf : (Real.exp (t / 2) / t ^ 12) / 2 ≤ (endpointTestCutoff t : ℝ) := by
    have h := Nat.sub_one_lt_floor (Real.exp (t / 2) / t ^ 12)
    change Real.exp (t / 2) / t ^ 12 - 1 < (endpointTestCutoff t : ℝ) at h
    linarith
  refine ⟨hQ, Nat.floor_le hrp.le, ?_⟩
  have h := Real.log_le_log (by positivity : 0 < (Real.exp (t / 2) / t ^ 12) / 2) hhalf
  rw [Real.log_div hrp.ne' (by norm_num),
    Real.log_div (Real.exp_ne_zero _) (pow_ne_zero 12 htp.ne'), Real.log_exp, Real.log_pow] at h
  exact h

theorem endpointTestThreshold_bounds (t : ℝ) (ht : 0 < t) :
    1 ≤ endpointTestThreshold t ∧
      Real.exp (t / 2) / t ^ 10 ≤ (endpointTestThreshold t : ℝ) ∧
      (endpointTestThreshold t : ℝ) < Real.exp (t / 2) / t ^ 10 + 1 := by
  have hr : 0 < Real.exp (t / 2) / t ^ 10 := by positivity
  exact ⟨Nat.one_le_ceil_iff.mpr hr, Nat.le_ceil _, Nat.ceil_lt_add_one hr.le⟩

theorem endpoint_test_collision_budget_le (t C : ℝ) (X : ℕ) (ht : 1 ≤ t)
    (hr : 2 ≤ Real.exp (t / 2) / t ^ 12) (hX : Real.log (X : ℝ) ≤ t) :
    2 * Real.log X - 4 * Real.log (endpointTestCutoff t : ℝ) + 4 * C +
      2 * (1 / (endpointTestThreshold t : ℝ)) * Real.log 4 * endpointTestCutoff t ≤
        48 * Real.log t + 4 * C + 4 * Real.log 2 + 2 * Real.log 4 := by
  have htp : 0 < t := by linarith
  have hQ := endpointTestCutoff_bounds t ht hr
  have hK := endpointTestThreshold_bounds t htp
  have hKp : (0 : ℝ) < endpointTestThreshold t := by exact_mod_cast (show 0 < endpointTestThreshold t by omega)
  have hQK : (endpointTestCutoff t : ℝ) / endpointTestThreshold t ≤ 1 := by
    calc
      _ ≤ (Real.exp (t / 2) / t ^ 12) / endpointTestThreshold t :=
        div_le_div_of_nonneg_right hQ.2.1 hKp.le
      _ ≤ (Real.exp (t / 2) / t ^ 12) / (Real.exp (t / 2) / t ^ 10) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hK.2.1
      _ = 1 / t ^ 2 := by field_simp
      _ ≤ 1 := (div_le_one (by positivity : 0 < t ^ 2)).mpr (one_le_pow₀ ht)
  have herr := mul_le_mul_of_nonneg_left hQK (show 0 ≤ 2 * Real.log 4 by positivity)
  have he : 2 * Real.log 4 * ((endpointTestCutoff t : ℝ) / endpointTestThreshold t) =
      2 * (1 / (endpointTestThreshold t : ℝ)) * Real.log 4 * endpointTestCutoff t := by ring
  rw [he] at herr
  linarith [hQ.2.2]

theorem eventual_endpointTestCutoff :
    ∀ᶠ t : ℝ in atTop, 1 ≤ t ∧ 2 ≤ Real.exp (t / 2) / t ^ 12 := by
  have hb := ((isLittleO_pow_exp_pos_mul_atTop 12 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul_left 2).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with t hb ht
  have htp : 0 < t := by linarith
  have hpow : 2 * t ^ 12 ≤ Real.exp (t / 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) * t ^ 12),
      abs_of_pos (Real.exp_pos _), one_mul, one_div_mul_eq_div] using hb
  exact ⟨ht, (le_div_iff₀ (pow_pos htp 12)).mpr hpow⟩

theorem endpointTestCutoff_le_tailCollisionCutoff (t : ℝ) (ht : 1 ≤ t) :
    endpointTestCutoff t ≤ tailCollisionCutoff t := by
  apply Nat.floor_mono
  have htp : 0 < t := by linarith
  apply div_le_div_of_nonneg_left (Real.exp_nonneg _) (pow_pos htp 5)
  exact pow_le_pow_right₀ ht (by decide : 5 ≤ 12)

theorem eventual_endpointTestCutoff_quarter :
    ∀ᶠ t : ℝ in atTop, Real.exp (t / 4) ≤ (endpointTestCutoff t : ℝ) := by
  have hb := ((isLittleO_pow_exp_pos_mul_atTop 12 (by norm_num : (0 : ℝ) < 1 / 4)).const_mul_left 2).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb, eventual_endpointTestCutoff] with t hb ht
  have htp : 0 < t := by linarith [ht.1]
  have hpow : 2 * t ^ 12 ≤ Real.exp (t / 4) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) * t ^ 12),
      abs_of_pos (Real.exp_pos _), one_mul, one_div_mul_eq_div] using hb
  have hexp : Real.exp (t / 4) * Real.exp (t / 4) = Real.exp (t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmul := mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg (t / 4))
  rw [hexp] at hmul
  have hratio : 2 * Real.exp (t / 4) ≤ Real.exp (t / 2) / t ^ 12 := by
    apply (le_div_iff₀ (pow_pos htp 12)).mpr
    nlinarith only [hmul]
  have hf := Nat.sub_one_lt_floor (Real.exp (t / 2) / t ^ 12)
  change Real.exp (t / 2) / t ^ 12 - 1 < (endpointTestCutoff t : ℝ) at hf
  have hone : 1 ≤ Real.exp (t / 4) := Real.one_le_exp (by positivity)
  linarith

theorem eventual_endpoint_test_error_small (α β D C δ c : ℝ)
    (hα : 0 < α) (hδ : 0 < δ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ t : ℝ, Real.log t ≤ β * L + D →
      4 * ((48 * Real.log t + 4 * C + 4 * Real.log 2 + 2 * Real.log 4) /
        Real.exp (α * L)) < δ ^ 2 * c := by
  have hlin : Tendsto (fun L : ℝ => L * Real.exp (-α * L)) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 α hα
  have hconst : Tendsto (fun L : ℝ => Real.exp (-α * L)) atTop (nhds 0) := by
    simpa only [Real.rpow_zero, one_mul] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 α hα
  have hbound : Tendsto (fun L : ℝ =>
      4 * ((48 * (β * L + D) + 4 * C + 4 * Real.log 2 + 2 * Real.log 4) /
        Real.exp (α * L))) atTop (nhds 0) := by
    have h := (hlin.const_mul (192 * β)).add
      (hconst.const_mul (192 * D + 16 * C + 16 * Real.log 2 + 8 * Real.log 4))
    simp only [mul_zero, add_zero] at h
    apply h.congr
    intro L
    rw [div_eq_mul_inv, ← Real.exp_neg]
    simp only [neg_mul]
    ring
  filter_upwards [hbound.eventually_lt_const (by positivity : (0 : ℝ) < δ ^ 2 * c)] with L hL t ht
  apply lt_of_le_of_lt _ hL
  gcongr

theorem eventual_endpoint_test_threshold_negligible (a : ℝ) (ha : 0 < a) (J : ℕ) :
    ∀ᶠ t : ℝ in atTop,
      (J : ℝ) * endpointTestThreshold t ≤ (a / 2) * Real.exp (t / 2) / t ^ 3 := by
  have hpow : Tendsto (fun t : ℝ => t ^ 7) atTop atTop := tendsto_pow_atTop (by decide)
  have hpoly := ((isLittleO_pow_exp_pos_mul_atTop 3 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul_left
    (4 * J / a)).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hpow.eventually_ge_atTop (4 * J / a), hpoly,
    eventually_ge_atTop (1 : ℝ)] with t ht hpoly ht1
  have htp : 0 < t := by linarith
  have hK := (endpointTestThreshold_bounds t htp).2.2.le
  have h1 : (J : ℝ) * (Real.exp (t / 2) / t ^ 10) ≤
      (a / 4) * Real.exp (t / 2) / t ^ 3 := by
    have hJa : (J : ℝ) ≤ (a / 4) * t ^ 7 := by
      have h := (div_le_iff₀ ha).mp ht
      nlinarith only [h]
    have h := mul_le_mul_of_nonneg_right hJa (by positivity : 0 ≤ Real.exp (t / 2) / t ^ 10)
    convert h using 1
    field_simp
  have h2 : (J : ℝ) ≤ (a / 4) * Real.exp (t / 2) / t ^ 3 := by
    have h : (4 * J / a) * t ^ 3 ≤ Real.exp (t / 2) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (4 * (J : ℝ) / a) * t ^ 3),
        abs_of_pos (Real.exp_pos _), one_mul, one_div_mul_eq_div] using hpoly
    apply (le_div_iff₀ (pow_pos htp 3)).mpr
    have h' := mul_le_mul_of_nonneg_right h (show 0 ≤ a / 4 by positivity)
    have he : ((4 * J / a) * t ^ 3) * (a / 4) = (J : ℝ) * t ^ 3 := by field_simp
    rw [he] at h'
    nlinarith only [h']
  have h := mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg (α := ℝ) J)
  rw [mul_add, mul_one] at h
  have he : (a / 2) * Real.exp (t / 2) / t ^ 3 =
      2 * ((a / 4) * Real.exp (t / 2) / t ^ 3) := by ring
  rw [he]
  linarith

end Ostmann

end OAI
