import OAI.Combinatorics.ProgressionColoring.Asymptotics
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace OAI

noncomputable section

open Filter Topology

namespace QuantitativeVanDerWaerden.Parameters

theorem log_prime_slack {k : ℕ} (hk : 2 ≤ k) :
    Real.log (2 * (k : ℝ) ^ 2) ≤ 3 * Real.log k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hl : Real.log 2 ≤ Real.log k :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hk)
  rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hk0.ne'), Real.log_pow]
  norm_num
  linarith

theorem log_two_le_power_log {k : ℕ} (hk : 2 ≤ k) {a : ℝ} (ha : 0 ≤ a) :
    Real.log 2 ≤ (k : ℝ) ^ a * Real.log k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hl : Real.log 2 ≤ Real.log k :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hk)
  calc
    Real.log 2 ≤ Real.log k := hl
    _ ≤ (k : ℝ) ^ a * Real.log k :=
      le_mul_of_one_le_left (Real.log_nonneg hk1) (Real.one_le_rpow hk1 ha)

/-- The exact exponent appearing in the rich-progression union bound. -/
def richEnvelope (k : ℕ) : ℝ :=
  Real.exp (-(21 / 200000 : ℝ) * k * Real.log k +
    2 * dimension k * Real.log (2 * (k : ℝ) ^ 2) + Real.log 2)

theorem richEnvelope_tendsto : Tendsto richEnvelope atTop (𝓝 0) := by
  have hb : ∀ᶠ k : ℕ in atTop, richEnvelope k ≤
      Real.exp (13 * (k : ℝ) ^ (1 / 10 : ℝ) * Real.log k -
        (21 / 200000 : ℝ) * (k : ℝ) ^ (1 : ℝ)) := by
    have hl := (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop)).eventually
      (eventually_ge_atTop (1 : ℝ))
    filter_upwards [eventually_ge_atTop 2, hl] with k hk hlog
    have hk1 : 1 ≤ k := by omega
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hD := dimension_upper hk1
    have hL := log_prime_slack hk
    have hL0 : 0 ≤ Real.log (2 * (k : ℝ) ^ 2) := by
      apply Real.log_nonneg
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    have hDL : 2 * (dimension k : ℝ) * Real.log (2 * (k : ℝ) ^ 2) ≤
        12 * (k : ℝ) ^ (1 / 10 : ℝ) * Real.log k := by
      calc
        _ ≤ (4 * (k : ℝ) ^ (1 / 10 : ℝ)) * Real.log (2 * (k : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) hL0
        _ ≤ (4 * (k : ℝ) ^ (1 / 10 : ℝ)) * (3 * Real.log k) :=
          mul_le_mul_of_nonneg_left hL (by positivity)
        _ = _ := by ring
    have htwo := log_two_le_power_log hk (by norm_num : (0 : ℝ) ≤ 1 / 10)
    have hklog : (k : ℝ) ≤ (k : ℝ) * Real.log k :=
      le_mul_of_one_le_right hk0 hlog
    apply Real.exp_le_exp.mpr
    simp only [Real.rpow_one]
    nlinarith
  apply squeeze_zero' (Eventually.of_forall fun k => (Real.exp_pos _).le) hb
  exact Scaling.tendsto_exp_rpow_log_sub_rpow (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- Envelope for twice the affine-signature count times the survival bound. -/
def affineEnvelope (C : ℝ) (k : ℕ) : ℝ :=
  Real.exp ((C + 1) * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log k -
    (1 / 4 : ℝ) * (k : ℝ) ^ (19 / 20 : ℝ))

theorem affineEnvelope_tendsto {C : ℝ} (hC : 0 ≤ C) :
    Tendsto (affineEnvelope C) atTop (𝓝 0) := by
  exact Scaling.tendsto_exp_rpow_log_sub_rpow (by norm_num) (by linarith)
    (by norm_num) (by norm_num)

theorem affine_risk_le {k : ℕ} (hk : 2 ≤ k) {C T : ℝ}
    (hT : 0 < T)
    (hentropy : Real.log T ≤ C * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log k) :
    2 * T * Real.exp (-(flipProbability k * k) / 4) ≤ affineEnvelope C k := by
  have htwo := log_two_le_power_log hk (by norm_num : (0 : ℝ) ≤ 9 / 10)
  have hmass := flip_mass (by omega : 0 < k)
  calc
    2 * T * Real.exp (-(flipProbability k * k) / 4) =
        Real.exp (Real.log 2 + Real.log T - (flipProbability k * k) / 4) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_add,
        Real.exp_log (by norm_num), Real.exp_log hT, neg_div]
    _ ≤ affineEnvelope C k := by
      apply Real.exp_le_exp.mpr
      rw [hmass]
      nlinarith

/-- A global-row envelope, from `log T ≤ C k^(3/10) log k`. -/
def rowEnvelope (C : ℝ) (k : ℕ) : ℝ :=
  Real.exp ((C + 2) * (k : ℝ) ^ (3 / 10 : ℝ) * Real.log k -
    (1 / 320 : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ))

theorem rowEnvelope_tendsto {C : ℝ} (hC : 0 ≤ C) :
    Tendsto (rowEnvelope C) atTop (𝓝 0) := by
  exact Scaling.tendsto_exp_rpow_log_sub_rpow (by norm_num) (by linarith)
    (by norm_num) (by norm_num)

theorem eventually_row_risk_le (C : ℝ) : ∀ᶠ k : ℕ in atTop,
    ∀ T : ℝ, 0 < T →
      Real.log T ≤ C * (k : ℝ) ^ (3 / 10 : ℝ) * Real.log k →
      (k : ℝ) * T * Real.exp (-((cutoff k : ℝ) / 10 - 1) / 32) ≤ rowEnvelope C k := by
  have hl := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop)).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventually_ge_atTop 2, hl] with k hk hlog T hT hentropy
  change 1 ≤ Real.log (k : ℝ) at hlog
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hp : 1 ≤ (k : ℝ) ^ (3 / 10 : ℝ) := Real.one_le_rpow hk1 (by norm_num)
  have hlogbound : Real.log k ≤ (k : ℝ) ^ (3 / 10 : ℝ) * Real.log k :=
    le_mul_of_one_le_left (by linarith) hp
  have hunit : 1 ≤ (k : ℝ) ^ (3 / 10 : ℝ) * Real.log k :=
    one_le_mul_of_one_le_of_one_le hp hlog
  have hM := cutoff_lower k
  calc
    (k : ℝ) * T * Real.exp (-((cutoff k : ℝ) / 10 - 1) / 32) =
        Real.exp (Real.log k + Real.log T - ((cutoff k : ℝ) / 10 - 1) / 32) := by
      simp only [Real.exp_sub, Real.exp_add, Real.exp_log hk0,
        Real.exp_log hT, Real.exp_neg, div_eq_mul_inv, neg_mul]
    _ ≤ rowEnvelope C k := by
      apply Real.exp_le_exp.mpr
      nlinarith

/-- One threshold suffices to make both perturbation union bounds less than one.
The scalar entropy constant is fixed before the number of colors is introduced. -/
theorem eventually_perturbation_budget {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ k : ℕ in atTop, richEnvelope k + affineEnvelope C k < 1 := by
  have ht := richEnvelope_tendsto.add (affineEnvelope_tendsto hC)
  have he := ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) + 0 < 1))
  exact he

end QuantitativeVanDerWaerden.Parameters

end

end OAI
