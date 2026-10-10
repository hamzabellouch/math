import OAI.NumberTheory.TwoPoint.Fourier.MinorArcTheorem
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! First-band parameters. A larger fixed lower-endpoint power absorbs
the explicit factorial constants; it changes only the absolute constant. -/

namespace TwoPointCorrelations

open Filter

noncomputable def minorArcFirstLower (A : ℕ) (H : ℝ) : ℝ := (Real.log H) ^ (5 * A)

noncomputable def minorArcFirstUpper (H : ℝ) : ℝ := H / (Real.log H) ^ 15

lemma minor_arc_first_lower_log (A : ℕ) (H : ℝ) :
    Real.log (minorArcFirstLower A H) = 5 * (A : ℝ) * Real.log (Real.log H) := by
  simp only [minorArcFirstLower, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]

lemma minor_arc_first_band_budget (A : ℕ) (hA : 500000 ≤ A) (H : ℝ)
    (hloglog : 1 ≤ Real.log (Real.log H)) (hQ : 1 < minorArcFirstUpper H)
    (hQH : minorArcFirstUpper H ≤ H) :
    8192 * (Real.log (Real.log (minorArcFirstUpper H)) + 1) ≤
      (1 / 100 : ℝ) * Real.log (minorArcFirstLower A H) := by
  have hmono := Real.log_le_log (Real.log_pos hQ)
    (Real.log_le_log (by linarith : 0 < minorArcFirstUpper H) hQH)
  have hA' : (500000 : ℝ) ≤ A := by exact_mod_cast hA
  have hm := mul_le_mul_of_nonneg_right hA' (by linarith : 0 ≤ Real.log (Real.log H))
  rw [minor_arc_first_lower_log]
  nlinarith

lemma minor_arc_first_band_density (A : ℕ) (H : ℝ)
    (hL : 0 < Real.log H) (hLL : 0 ≤ Real.log (Real.log H))
    (hQ : Real.log H / 2 ≤ Real.log (minorArcFirstUpper H)) :
    Real.log (minorArcFirstLower A H) / Real.log (minorArcFirstUpper H) ≤
      10 * (A : ℝ) * Real.log (Real.log H) / Real.log H := by
  rw [minor_arc_first_lower_log]
  calc
    _ ≤ (5 * (A : ℝ) * Real.log (Real.log H)) / (Real.log H / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hQ
    _ = _ := by ring

theorem minor_arc_first_band_scale (A R₀ : ℕ) (hA : 2 ≤ A) :
    ∀ᶠ H : ℝ in atTop, 4 ≤ H ∧ 2 ≤ Real.log H ∧ 1 ≤ Real.log (Real.log H) ∧
      4 ≤ minorArcFirstLower A H ∧ 2 * (R₀ : ℝ) ≤ minorArcFirstLower A H ∧
      2 * (Real.log H) ^ 5 ≤ minorArcFirstLower A H ∧
      minorArcFirstLower A H ≤ minorArcFirstUpper H ∧
      minorArcFirstUpper H ≤ H / (Real.log H) ^ 5 ∧
      (Real.log H) / 2 ≤ Real.log (minorArcFirstUpper H) ∧
      1 ≤ Real.log (minorArcFirstUpper H) := by
  let E : ℕ := max (5 * A + 15) 30
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := E)).bound (by norm_num : (0 : ℝ) < 1)
  have hlarge := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max (4 : ℝ) (2 * R₀)))
  have hloglog := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hsmall, hlarge, hloglog, eventually_ge_atTop (4 : ℝ)] with H hs hl hll hH
  have hL4 : 4 ≤ Real.log H := (le_max_left _ _).trans hl
  have hLR : 2 * (R₀ : ℝ) ≤ Real.log H := (le_max_right _ _).trans hl
  have hL1 : 1 ≤ Real.log H := by linarith
  have hL0 : 0 < Real.log H := by linarith
  have hH0 : 0 < H := by linarith
  dsimp only [id] at hs
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hL0.le E), Real.norm_eq_abs,
    abs_of_pos hH0, one_mul] at hs
  have hsA : Real.log H ^ (5 * A + 15) ≤ H :=
    (pow_le_pow_right₀ hL1 (le_max_left _ _)).trans hs
  have hs30 : Real.log H ^ 30 ≤ H :=
    (pow_le_pow_right₀ hL1 (le_max_right _ _)).trans hs
  have hP0 : 0 < minorArcFirstLower A H := by unfold minorArcFirstLower; positivity
  have hPL : Real.log H ≤ minorArcFirstLower A H :=
    le_self_pow₀ hL1 (by omega : 5 * A ≠ 0)
  have hPQ : minorArcFirstLower A H ≤ minorArcFirstUpper H := by
    apply (le_div_iff₀ (pow_pos hL0 15)).mpr
    simpa only [minorArcFirstLower, ← pow_add] using hsA
  have hW2 : 2 ≤ Real.log H ^ 5 :=
    (by linarith : 2 ≤ Real.log H).trans (le_self_pow₀ hL1 (by norm_num : (5 : ℕ) ≠ 0))
  have hWP : 2 * Real.log H ^ 5 ≤ minorArcFirstLower A H := by
    have hpow := pow_le_pow_right₀ (by linarith : 1 ≤ Real.log H ^ 5) hA
    have hbase : 2 * Real.log H ^ 5 ≤ (Real.log H ^ 5) ^ 2 := by nlinarith
    exact hbase.trans (by simpa only [pow_mul, minorArcFirstLower] using hpow)
  have hQU : minorArcFirstUpper H ≤ H / Real.log H ^ 5 :=
    div_le_div_of_nonneg_left hH0.le (pow_pos hL0 5)
      (pow_le_pow_right₀ hL1 (by norm_num : 5 ≤ 15))
  have h30 := Real.log_le_log (pow_pos hL0 30) hs30
  rw [Real.log_pow] at h30
  norm_num at h30
  have hlogQ : Real.log (minorArcFirstUpper H) = Real.log H - 15 * Real.log (Real.log H) := by
    rw [minorArcFirstUpper, Real.log_div hH0.ne' (pow_ne_zero 15 hL0.ne'), Real.log_pow]
    norm_num
  have hhalf : Real.log H / 2 ≤ Real.log (minorArcFirstUpper H) := by rw [hlogQ]; linarith
  exact ⟨hH, by linarith, hll, hL4.trans hPL, hLR.trans hPL, hWP, hPQ, hQU,
    hhalf, by linarith⟩

theorem minor_arc_first_band_density_eventually (A : ℕ) (hA : 2 ≤ A) :
    ∀ᶠ H : ℝ in atTop,
      Real.log (minorArcFirstLower A H) / Real.log (minorArcFirstUpper H) ≤
        10 * (A : ℝ) * Real.log (Real.log H) / Real.log H := by
  filter_upwards [minor_arc_first_band_scale A 0 hA] with H hH
  obtain ⟨_, hL, hLL, _, _, _, _, _, hhalf, _⟩ := hH
  exact minor_arc_first_band_density A H (by linarith) (by linarith) hhalf

theorem minor_arc_first_band_budget_eventually (A : ℕ) (hA : 500000 ≤ A) :
    ∀ᶠ H : ℝ in atTop,
      8192 * (Real.log (Real.log (minorArcFirstUpper H)) + 1) ≤
        (1 / 100 : ℝ) * Real.log (minorArcFirstLower A H) := by
  filter_upwards [minor_arc_first_band_scale A 0 (by omega)] with H hs
  obtain ⟨hH, hL, hLL, hP, _hPR, _hPW, hPQ, hQU, _hhalf, _hQ⟩ := hs
  apply minor_arc_first_band_budget A hA H hLL (by linarith)
  exact hQU.trans (div_le_self (by linarith) (one_le_pow₀ (by linarith : 1 ≤ Real.log H)))

end TwoPointCorrelations

end OAI
