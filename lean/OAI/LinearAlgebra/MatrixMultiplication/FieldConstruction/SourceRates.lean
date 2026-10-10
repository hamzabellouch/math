import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.Source
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldSourceRates

open AllFieldSource Filter
open scoped Topology

private theorem tendsto_log_linear_div_nat (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => Real.log (a * N + 1) / (N : ℝ)) atTop (𝓝 0) := by
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have harg : Tendsto (fun N : ℕ => a * N + 1) atTop atTop :=
    (hnat.const_mul_atTop ha).atTop_add_nonneg (fun _ => zero_le_one)
  have hlog : Tendsto (fun N : ℕ => Real.log (a * N + 1) / (a * N + 1))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp harg
  have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnat
  have hratio : Tendsto (fun N : ℕ => (a * N + 1) / (N : ℝ)) atTop (𝓝 a) := by
    have hsum : Tendsto (fun N : ℕ => a + 1 / (N : ℝ)) atTop (𝓝 a) := by
      simpa only [add_zero] using hinv.const_add a
    apply hsum.congr'
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with N hN
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    field_simp [hN']
  have hprod : Tendsto (fun N : ℕ =>
      (Real.log (a * N + 1) / (a * N + 1)) * ((a * N + 1) / (N : ℝ)))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using hlog.mul hratio
  apply hprod.congr
  intro N
  have harg' : a * (N : ℝ) + 1 ≠ 0 := by positivity
  exact div_mul_div_cancel₀ harg'

theorem tendsto_log_polynomial_overhead (K : ℕ) (hK : 0 < K) :
    Tendsto (fun N : ℕ =>
      Real.log (((3 * (8 * K * N) + 1) ^ 2 : ℕ) : ℝ) / ((K : ℝ) * N))
      atTop (𝓝 0) := by
  have hK' : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hbase := tendsto_log_linear_div_nat (3 * (8 * (K : ℝ))) (by positivity)
  have hscaled : Tendsto (fun N : ℕ =>
      (2 * (Real.log (3 * (8 * (K : ℝ)) * N + 1) / (N : ℝ))) / (K : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div] using (hbase.const_mul 2).div_const (K : ℝ)
  apply hscaled.congr
  intro N
  have harg : ((3 * (8 * K * N) + 1 : ℕ) : ℝ) =
      3 * (8 * (K : ℝ)) * N + 1 := by push_cast; ring
  rw [Nat.cast_pow, Real.log_pow, harg]
  norm_num only [Nat.cast_ofNat]
  ring

theorem tendsto_log_exponential_source (K : ℕ) (hK : 0 < K) :
    Tendsto (fun N : ℕ =>
      Real.log ((7 ^ (8 * K * N) : ℕ) : ℝ) / ((K : ℝ) * N))
      atTop (𝓝 (8 * Real.log 7)) := by
  have hK' : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with N hN
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [Nat.cast_pow, Real.log_pow]
  push_cast
  field_simp [hK', hN']

theorem log_rankBudget (Copies : Type*) [Fintype Copies] (K N : ℕ)
    (hcopies : 0 < Fintype.card Copies) :
    Real.log (rankBudget Copies K N : ℝ) =
      Real.log (Fintype.card Copies : ℝ) +
        Real.log (((3 * (8 * K * N) + 1) ^ 2 : ℕ) : ℝ) +
        Real.log ((7 ^ (8 * K * N) : ℕ) : ℝ) := by
  have hc : (Fintype.card Copies : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hcopies)
  have hp : (((3 * (8 * K * N) + 1) ^ 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have he : ((7 ^ (8 * K * N) : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [rankBudget, Nat.cast_mul]
  rw [Real.log_mul hc (mul_ne_zero hp he), Real.log_mul hp he, ← add_assoc]

theorem tendsto_log_rankBudget (Copies : ℕ → Type*) [∀ N, Fintype (Copies N)]
    (K : ℕ) (hK : 0 < K)
    (hcopies : ∀ N, 0 < Fintype.card (Copies N))
    (hcopyRate : Tendsto (fun N : ℕ =>
      Real.log (Fintype.card (Copies N) : ℝ) / (N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      Real.log (rankBudget (Copies N) K N : ℝ) / ((K : ℝ) * N))
      atTop (𝓝 (8 * Real.log 7)) := by
  have hc : Tendsto (fun N : ℕ =>
      Real.log (Fintype.card (Copies N) : ℝ) / ((K : ℝ) * N)) atTop (𝓝 0) := by
    have h : Tendsto (fun N : ℕ =>
        (Real.log (Fintype.card (Copies N) : ℝ) / (N : ℝ)) / (K : ℝ))
        atTop (𝓝 0) := by
      simpa only [zero_div] using hcopyRate.div_const (K : ℝ)
    apply h.congr
    intro N
    ring
  have hsum := (hc.add (tendsto_log_polynomial_overhead K hK)).add
    (tendsto_log_exponential_source K hK)
  simp only [zero_add] at hsum
  apply hsum.congr
  intro N
  rw [log_rankBudget (Copies N) K N (hcopies N), add_div, add_div]

end MatrixMultiplication.AllFieldSourceRates

end

end OAI
