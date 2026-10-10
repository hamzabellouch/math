import OAI.MeasureTheory.Falconer.Incidence.PlanarIncidence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-!
# Rounding and scale budgets for planar sampling

The sample sizes are ceilings of the reciprocal dimension powers. Query
counts grow at most cubically in the reciprocal scale, while the chosen
exponential tail decays with the tenth power of that scale.
-/

namespace Falconer
open Real Filter
open scoped Topology

theorem sampling_ceil_size {δ s : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 ≤ s) :
    0 < Nat.ceil (δ^(-s)) ∧
      1 ≤ (Nat.ceil (δ^(-s)) : ℝ)*δ^s ∧
      (Nat.ceil (δ^(-s)) : ℝ)*δ^s ≤ 2 := by
  have hp : 0 < δ^(-s) := Real.rpow_pos_of_pos hδ _
  have hδs : δ^s ≤ 1 := Real.rpow_le_one hδ.le hδ1 hs
  have hprod : δ^(-s)*δ^s = 1 := by
    rw [← Real.rpow_add hδ, neg_add_cancel, Real.rpow_zero]
  refine ⟨Nat.ceil_pos.mpr hp, ?_, ?_⟩
  · exact hprod ▸ mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Real.rpow_nonneg hδ.le _)
  · have hh := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one hp.le).le
      (Real.rpow_nonneg hδ.le s)
    rw [add_mul, hprod, one_mul] at hh
    linarith

theorem sampling_query_card_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (((2 * Nat.ceil (δ⁻¹+1)+1)^2 * Nat.ceil δ⁻¹ : ℕ) : ℝ) ≤ 98*δ⁻¹^3 := by
  have hi : (1 : ℝ) ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  have hL := (Nat.ceil_lt_add_one (by positivity : 0 ≤ δ⁻¹+1)).le
  have hH := (Nat.ceil_lt_add_one (inv_nonneg.mpr hδ.le)).le
  have hLb : (2 * Nat.ceil (δ⁻¹+1)+1 : ℝ) ≤ 7*δ⁻¹ := by linarith
  have hHb : (Nat.ceil δ⁻¹ : ℝ) ≤ 2*δ⁻¹ := by linarith
  push_cast
  calc
    _ ≤ (7*δ⁻¹)^2 * (2*δ⁻¹) := mul_le_mul
      (pow_le_pow_left₀ (by positivity) hLb 2) hHb (by positivity) (by positivity)
    _ = _ := by ring

theorem sampling_exponential_tail {δ : ℝ} (hδ : 0 < δ) :
    exp (-(-10*log δ)) = δ^10 := by
  rw [show -(-10*log δ) = (10 : ℕ)*log δ by ring, Real.exp_nat_mul, Real.exp_log hδ]

theorem sampling_failure_bound {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/4) :
    (((2 * Nat.ceil (δ⁻¹+1)+1)^2 * Nat.ceil δ⁻¹ : ℕ) : ℝ) *
      exp (-(-10*log δ)) ≤ δ/16 := by
  rw [sampling_exponential_tail hδ]
  have hb := mul_le_mul_of_nonneg_right (sampling_query_card_bound hδ (by linarith))
    (pow_nonneg hδ.le 10)
  have he : (98*δ⁻¹^3)*δ^10 = 98*δ^7 := by
    field_simp
  rw [he] at hb
  have hh := pow_le_pow_left₀ hδ.le hδsmall 6
  have hf : 98*δ^7 ≤ δ/16 := by nlinarith [mul_le_mul_of_nonneg_left hh hδ.le]
  exact hb.trans hf

theorem sampling_log_budget {η : ℝ} (hη : 0 < η) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), -10*log δ ≤ δ^(-η) := by
  have h := (isLittleO_log_rpow_nhdsGT_zero (neg_neg_of_pos hη)).def
    (show (0 : ℝ) < 1/10 by norm_num)
  filter_upwards [h, self_mem_nhdsWithin] with δ hbound hδ
  have hδp : 0 < δ := hδ
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hδp _)] at hbound
  have hh := neg_le_abs (log δ)
  nlinarith

end Falconer

end OAI
