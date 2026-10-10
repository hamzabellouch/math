import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace OAI

/-!
# Compatible parameters and elementary asymptotics

The strict inequalities here are the weight margins of `arithmetic.tex`.
The subsequent limits account for the sampling entropy and the logarithmic
factors in the prime cutoff and amplification parameters.
-/

namespace JointDickman

open Filter Asymptotics
open scoped Topology

noncomputable def weightBaseExponent : ℝ := (1 - Real.log 2) / 2

noncomputable def weightExponent (τ : ℝ) : ℝ := weightBaseExponent + τ * Real.log 2

/-- One concrete choice satisfying all three weight margins. -/
noncomputable def samplingTau : ℝ := 1 / 1000

noncomputable def amplificationExponent : ℝ := (8 / 5) * Real.log 2

theorem samplingTau_pos : 0 < samplingTau := by norm_num [samplingTau]

theorem weightBaseExponent_pos : 0 < weightBaseExponent := by
  have h := Real.log_two_lt_d9
  unfold weightBaseExponent
  linarith

theorem amplificationExponent_gt_one : 1 < amplificationExponent := by
  have h := Real.log_two_gt_d9
  unfold amplificationExponent
  linarith

theorem weightExponent_mono : Monotone weightExponent := by
  intro a b hab
  unfold weightExponent
  have hmul := mul_le_mul_of_nonneg_right hab
    (Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num))
  linarith

theorem samplingTau_weight_margins :
    2 * weightExponent samplingTau < (32 / 100 : ℝ) ∧
      (7 / 100 : ℝ) < 1 - 6 * weightExponent samplingTau ∧
      (229 / 1000 : ℝ) < 1 - 5 * weightExponent samplingTau := by
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  unfold weightExponent weightBaseExponent samplingTau
  constructor
  · linarith
  constructor <;> linarith

/-- Every smaller nonnegative tolerance preserves the strict margins. -/
theorem weight_margins_of_le_samplingTau {τ : ℝ} (hτ : τ ≤ samplingTau) :
    2 * weightExponent τ < (32 / 100 : ℝ) ∧
      (7 / 100 : ℝ) < 1 - 6 * weightExponent τ ∧
      (229 / 1000 : ℝ) < 1 - 5 * weightExponent τ := by
  have hm := weightExponent_mono hτ
  obtain ⟨h₂, h₆, h₅⟩ := samplingTau_weight_margins
  constructor
  · linarith
  constructor <;> linarith

/-- A fixed power times a logarithm is smaller than any strictly larger
power. The base tends through positive reals. -/
theorem power_mul_log_isLittleO {a b : ℝ} (hab : a < b) :
    (fun B : ℝ => B ^ a * Real.log B) =o[atTop] (fun B => B ^ b) := by
  have h := (isLittleO_log_rpow_atTop (sub_pos.mpr hab)).mul_isBigO
    (isBigO_refl (fun B : ℝ => B ^ a) atTop)
  apply h.congr'
  · exact Eventually.of_forall (fun B => mul_comm _ _)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    rw [← Real.rpow_add hB]
    congr 1
    ring

theorem power_mul_log_div_power_tendsto_zero {a b : ℝ} (hab : a < b) :
    Tendsto (fun B : ℝ => (B ^ a * Real.log B) / B ^ b)
      atTop (𝓝 0) :=
  (power_mul_log_isLittleO hab).tendsto_div_nhds_zero

theorem sampling_entropy_isLittleO :
    (fun B : ℝ => B ^ (14 / 100 : ℝ) * Real.log B) =o[atTop]
      (fun B => B ^ (18 / 100 : ℝ)) :=
  power_mul_log_isLittleO (by norm_num)

/-- The union-bound entropy is absorbed by the negative concentration
exponent whenever the latter has a strictly larger positive power. -/
theorem exp_power_log_sub_power_tendsto_zero {a b c : ℝ}
    (hab : a < b) (hb : 0 < b) (hc : 0 < c) (C : ℝ) :
    Tendsto (fun B : ℝ => Real.exp (C * (B ^ a * Real.log B) - c * B ^ b))
      atTop (𝓝 0) := by
  have hquot : Tendsto (fun B : ℝ => C * ((B ^ a * Real.log B) / B ^ b) - c)
      atTop (𝓝 (-c)) := by
    simpa using ((power_mul_log_div_power_tendsto_zero hab).const_mul C).sub_const c
  have hexponent := hquot.neg_mul_atTop (by linarith) (tendsto_rpow_atTop hb)
  have heq : (fun B : ℝ => (C * ((B ^ a * Real.log B) / B ^ b) - c) * B ^ b)
      =ᶠ[atTop] (fun B => C * (B ^ a * Real.log B) - c * B ^ b) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    have hpow := (Real.rpow_pos_of_pos hB b).ne'
    field_simp
  exact Real.tendsto_exp_atBot.comp (hexponent.congr' heq)

theorem sampling_union_bound_tendsto_zero {c : ℝ} (hc : 0 < c) (C : ℝ) :
    Tendsto (fun B : ℝ => Real.exp
      (C * (B ^ (14 / 100 : ℝ) * Real.log B) - c * B ^ (18 / 100 : ℝ)))
      atTop (𝓝 0) :=
  exp_power_log_sub_power_tendsto_zero (by norm_num) (by norm_num) hc C

/-- Every smaller real power is negligible compared with a larger one. -/
theorem power_div_power_tendsto_zero {a b : ℝ} (hab : a < b) :
    Tendsto (fun B : ℝ => B ^ a / B ^ b) atTop (𝓝 0) := by
  have h := tendsto_rpow_neg_atTop (sub_pos.mpr hab)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
  rw [← Real.rpow_sub hB]
  congr 1
  ring

/-- In particular, each fixed polynomial degree below the cutoff exponent
is negligible compared with `P₀ = B^1000`. -/
theorem polynomial_div_primeCutoff_tendsto_zero {k : ℕ} (hk : k < 1000) :
    Tendsto (fun B : ℝ => B ^ k / B ^ (1000 : ℕ)) atTop (𝓝 0) := by
  have h : (k : ℝ) < (1000 : ℝ) := by exact_mod_cast hk
  have hlim := power_div_power_tendsto_zero h
  change Tendsto (fun B : ℝ => B ^ (k : ℝ) / B ^ ((1000 : ℕ) : ℝ))
    atTop (𝓝 0) at hlim
  simpa only [Real.rpow_natCast] using hlim

/-- Fixed logarithmic powers are smaller than every positive real power. -/
theorem log_power_div_power_tendsto_zero (r : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun B : ℝ => (Real.log B) ^ r / B ^ s) atTop (𝓝 0) :=
  (isLittleO_log_rpow_rpow_atTop r hs).tendsto_div_nhds_zero

/-- The amplification loss `B/R^α`, with `R=B/(1000 log B)`, vanishes for
every `α>1`. This is the exact expression before introducing `R`. -/
theorem amplification_log_loss_tendsto_zero {α : ℝ} (hα : 1 < α) :
    Tendsto (fun B : ℝ => B * (1000 * Real.log B) ^ α / B ^ α)
      atTop (𝓝 0) := by
  have h := (log_power_div_power_tendsto_zero α (sub_pos.mpr hα)).const_mul
    ((1000 : ℝ) ^ α)
  have heq : (fun B : ℝ => (1000 : ℝ) ^ α * ((Real.log B) ^ α / B ^ (α - 1)))
      =ᶠ[atTop] (fun B => B * (1000 * Real.log B) ^ α / B ^ α) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with B hB
    have hB0 : 0 < B := lt_trans zero_lt_one hB
    have hpow : B ^ α ≠ 0 := (Real.rpow_pos_of_pos hB0 α).ne'
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1000) (Real.log_nonneg hB.le),
      Real.rpow_sub hB0, Real.rpow_one]
    field_simp
  simpa only [mul_zero] using h.congr' heq

theorem amplification_log_loss :
    Tendsto (fun B : ℝ => B * (1000 * Real.log B) ^ amplificationExponent /
      B ^ amplificationExponent) atTop (𝓝 0) :=
  amplification_log_loss_tendsto_zero amplificationExponent_gt_one

end JointDickman

end OAI
