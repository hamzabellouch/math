import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-! Ceiling parameters and dimension-ratio asymptotics. -/
noncomputable section
namespace Dixmier
open Filter Topology

def endpointCapacity (d : ℕ) (ρ : ℝ) (ℓ : ℕ) : ℕ := ⌈(d : ℝ)^ℓ * ρ^ℓ⌉₊
def fiberDimension (d : ℕ) (ρ : ℝ) (ℓ : ℕ) : ℕ :=
  ⌈2 * (endpointCapacity d ρ ℓ : ℝ) * Real.log (2 * (d : ℝ)^ℓ)⌉₊

theorem dimension_ratio_bound {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ} (hρ : 0 ≤ ρ) (ℓ : ℕ) :
    (fiberDimension d ρ ℓ : ℝ) / (d : ℝ)^ℓ ≤
      2 * (ρ^ℓ + 1 / (d : ℝ)^ℓ) * Real.log (2 * (d : ℝ)^ℓ) + 1 / (d : ℝ)^ℓ := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hn : (0 : ℝ) < (d : ℝ)^ℓ := pow_pos (lt_of_lt_of_le zero_lt_one hdR) _
  have hn1 : (1 : ℝ) ≤ (d : ℝ)^ℓ := one_le_pow₀ hdR
  have hlog : 0 ≤ Real.log (2 * (d : ℝ)^ℓ) := Real.log_nonneg (by nlinarith)
  have hr : (endpointCapacity d ρ ℓ : ℝ) ≤ (d : ℝ)^ℓ * ρ^ℓ + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hn.le (pow_nonneg hρ _))).le
  have hk : (fiberDimension d ρ ℓ : ℝ) ≤
      2 * (endpointCapacity d ρ ℓ : ℝ) * Real.log (2 * (d : ℝ)^ℓ) + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg (by positivity) hlog)).le
  have hk' : (fiberDimension d ρ ℓ : ℝ) ≤
      2 * ((d : ℝ)^ℓ * ρ^ℓ + 1) * Real.log (2 * (d : ℝ)^ℓ) + 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hr hlog]
  apply (div_le_iff₀ hn).mpr
  calc
    (fiberDimension d ρ ℓ : ℝ) ≤ 2 * ((d : ℝ)^ℓ * ρ^ℓ + 1) * Real.log (2 * (d : ℝ)^ℓ) + 1 := hk'
    _ = (2 * (ρ^ℓ + 1 / (d : ℝ)^ℓ) * Real.log (2 * (d : ℝ)^ℓ) + 1 / (d : ℝ)^ℓ) * (d : ℝ)^ℓ := by
      field_simp

/-- The logarithm contributes only a linear factor in the word length. -/
theorem geometric_log_tendsto {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {d : ℝ} (hd : 0 < d) :
    Tendsto (fun ℓ : ℕ => a^ℓ * Real.log (2 * d^ℓ)) atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one ha ha1
  have hl : Tendsto (fun ℓ : ℕ => (ℓ : ℝ) * a^ℓ) atTop (𝓝 0) := by
    simpa only [pow_one] using (summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖a‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg ha] using ha1)).tendsto_atTop_zero
  have h := (hp.mul_const (Real.log 2)).add (hl.mul_const (Real.log d))
  simp only [zero_mul, zero_add] at h
  convert h using 1
  ext ℓ
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hd.ne'), Real.log_pow]
  ring

/-- The dimension ratio tends to zero. -/
theorem dimension_ratio_tendsto {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun ℓ : ℕ => (fiberDimension d ρ ℓ : ℝ) / (d : ℝ)^ℓ) atTop (𝓝 0) := by
  have hdR : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
  have hi0 : (0 : ℝ) ≤ (d : ℝ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hi1 : (d : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr hdR
  have h1 := geometric_log_tendsto hρ hρ1 (lt_trans zero_lt_one hdR)
  have h2 := geometric_log_tendsto hi0 hi1 (lt_trans zero_lt_one hdR)
  have h3 := tendsto_pow_atTop_nhds_zero_of_lt_one hi0 hi1
  have hu : Tendsto (fun ℓ : ℕ =>
      2 * (ρ^ℓ + 1 / (d : ℝ)^ℓ) * Real.log (2 * (d : ℝ)^ℓ) + 1 / (d : ℝ)^ℓ)
      atTop (𝓝 0) := by
    have hh := ((h1.add h2).const_mul 2).add h3
    simp only [zero_add, mul_zero] at hh
    convert hh using 1
    ext ℓ
    simp only [one_div, inv_pow]
    ring
  exact squeeze_zero (fun ℓ => div_nonneg (Nat.cast_nonneg _) (by positivity))
    (dimension_ratio_bound hd hρ) hu

theorem endpointCapacity_pos {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ} (hρ : 0 < ρ) (ℓ : ℕ) :
    0 < endpointCapacity d ρ ℓ := by
  apply Nat.ceil_pos.mpr
  exact mul_pos (pow_pos (by exact_mod_cast (by omega : 0 < d)) _) (pow_pos hρ _)

theorem fiberDimension_pos {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ} (hρ : 0 < ρ) (ℓ : ℕ) :
    0 < fiberDimension d ρ ℓ := by
  have hr : (0 : ℝ) < endpointCapacity d ρ ℓ := by exact_mod_cast endpointCapacity_pos hd hρ ℓ
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hn1 : (1 : ℝ) ≤ (d : ℝ)^ℓ := one_le_pow₀ hdR
  have hlog : 0 < Real.log (2 * (d : ℝ)^ℓ) := Real.log_pos (by nlinarith)
  apply Nat.ceil_pos.mpr
  exact mul_pos (mul_pos (by norm_num) hr) hlog

/-- Reciprocal dimension ratio used by the direct-sum obstruction. -/
theorem reciprocal_dimension_ratio_tendsto {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    Tendsto (fun ℓ : ℕ => (d : ℝ)^ℓ / (fiberDimension d ρ ℓ : ℝ)) atTop atTop := by
  have ht : Tendsto (fun ℓ : ℕ => (fiberDimension d ρ ℓ : ℝ) / (d : ℝ)^ℓ)
      atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨dimension_ratio_tendsto hd hρ.le hρ1, Filter.Eventually.of_forall (fun ℓ => ?_)⟩
    change 0 < (fiberDimension d ρ ℓ : ℝ) / (d : ℝ)^ℓ
    apply div_pos
    · exact_mod_cast fiberDimension_pos hd hρ ℓ
    · exact pow_pos (by exact_mod_cast (by omega : 0 < d)) _
  simpa only [Function.comp_def, inv_div] using tendsto_inv_nhdsGT_zero.comp ht

/-- A kernel energy satisfying the cardinality lower bound has
unbounded energy per fibre dimension. -/
theorem energy_ratio_tendsto {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (E : ℕ → ℝ)
    (hE : ∀ ℓ, (d : ℝ)^ℓ ≤ E ℓ) :
    Tendsto (fun ℓ => E ℓ / (fiberDimension d ρ ℓ : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono _ (reciprocal_dimension_ratio_tendsto hd hρ hρ1)
  intro ℓ
  exact div_le_div_of_nonneg_right (hE ℓ) (Nat.cast_nonneg _)

end Dixmier

end

end OAI
