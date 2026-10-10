import OAI.Probability.SLE.Gauge.CoverNumerics
import OAI.Probability.SLE.Gauge.CoverMesh

namespace OAI

/-! The actual logarithmic choice of dense-visit multiplicity and the
linear test window used in the explicit gauge cover. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

def coverMultiplicity (c : ℝ) (n : ℕ) : ℕ :=
  ⌊c * Real.sqrt (Real.log (n : ℝ))⌋₊

def coverTestWindow (n : ℕ) : Finset ℕ := Finset.Icc (n / 3) (2 * n / 3)

theorem coverTestWindow_card_lower (n : ℕ) : n / 4 ≤ (coverTestWindow n).card := by
  simp only [coverTestWindow, Nat.card_Icc]
  omega

theorem coverTestWindow_card_real_lower (n : ℕ) :
    (n : ℝ) / 4 ≤ ((coverTestWindow n).card : ℝ) := by
  have hh : n ≤ 4 * (coverTestWindow n).card := by
    simp only [coverTestWindow, Nat.card_Icc]
    omega
  have hh' : (n : ℝ) ≤ 4 * ((coverTestWindow n).card : ℝ) := by exact_mod_cast hh
  linarith

theorem coverMultiplicity_upper {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    (coverMultiplicity c n : ℝ) ≤ c * Real.sqrt (Real.log (n : ℝ)) :=
  Nat.floor_le (mul_nonneg hc (Real.sqrt_nonneg _))

theorem coverMultiplicity_eventually_lower {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      c / 2 * Real.sqrt (Real.log (n : ℝ)) ≤ (coverMultiplicity c n : ℝ) := by
  have hlim : Tendsto (fun n : ℕ => c * Real.sqrt (Real.log (n : ℝ))) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop)).const_mul_atTop hc
  filter_upwards [hlim.eventually_ge_atTop 2] with n hn
  have hh := Nat.lt_floor_add_one (c * Real.sqrt (Real.log (n : ℝ)))
  change _ < (coverMultiplicity c n : ℝ) + 1 at hh
  linarith

theorem coverMultiplicity_eventually_ge {c : ℝ} (hc : 0 < c) (m₀ : ℕ) :
    ∀ᶠ n : ℕ in atTop, m₀ ≤ coverMultiplicity c n := by
  have hlim : Tendsto (fun n : ℕ => c * Real.sqrt (Real.log (n : ℝ))) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop)).const_mul_atTop hc
  filter_upwards [hlim.eventually_ge_atTop (m₀ : ℝ)] with n hn
  exact Nat.le_floor hn

/-- The mass created by the prescribed integer multiplicity is at least
the logarithmic correction of the explicit gauge. -/
theorem coverMultiplicity_mass_lower {c p : ℝ} (hc : 0 < c) (hp : 0 ≤ p) :
    ∀ᶠ n : ℕ in atTop,
      (c / 2) ^ p * (Real.log (n : ℝ)) ^ (p / 2) ≤
        (coverMultiplicity c n : ℝ) ^ p := by
  filter_upwards [coverMultiplicity_eventually_lower hc,
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  calc
    _ = (c / 2 * Real.sqrt (Real.log (n : ℝ))) ^ p := by
      rw [Real.mul_rpow (by positivity) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
        ← Real.rpow_mul hlog]
      congr 2
      ring
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hn hp

/-- A fixed dense-visit probability becomes at least `n^(-1/2)` at the
logarithmic multiplicity. The prefactor is retained, rather than discarded. -/
theorem denseVisit_probability_eventually_lower
    {a C c : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hc : 0 < c)
    (hsmall : C * c ^ 2 ≤ 1 / 4) :
    ∀ᶠ n : ℕ in atTop,
      1 / Real.sqrt (n : ℝ) ≤
        a * Real.exp (-C * (coverMultiplicity c n : ℝ) ^ 2) := by
  have hloglim : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hloglim.eventually_ge_atTop (-4 * Real.log a)] with n hn hlarge
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans_le hn)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hup := coverMultiplicity_upper hc.le n
  have hsq : (coverMultiplicity c n : ℝ) ^ 2 ≤ c ^ 2 * Real.log (n : ℝ) := by
    calc
      _ ≤ (c * Real.sqrt (Real.log (n : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hup 2
      _ = _ := by rw [mul_pow, Real.sq_sqrt hlog]
  have hCbound : C * (coverMultiplicity c n : ℝ) ^ 2 ≤ Real.log (n : ℝ) / 4 := by
    calc
      _ ≤ C * (c ^ 2 * Real.log (n : ℝ)) := mul_le_mul_of_nonneg_left hsq hC
      _ = (C * c ^ 2) * Real.log (n : ℝ) := by ring
      _ ≤ (1 / 4) * Real.log (n : ℝ) := mul_le_mul_of_nonneg_right hsmall hlog
      _ = _ := by ring
  have hsqrt : 1 / Real.sqrt (n : ℝ) = Real.exp (-(Real.log (n : ℝ) / 2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnpos, one_div, ← Real.exp_neg]
    congr 1
    ring
  rw [hsqrt, ← Real.exp_log ha, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end SLEExactGauge

end

end OAI
