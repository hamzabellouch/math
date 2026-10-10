import OAI.InformationTheory.BooleanNoise.EntropyScalars
import Mathlib.Analysis.PSeries

namespace OAI

noncomputable section

open Set Filter Finset
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

def psiCoeff (k : ℕ) : ℝ := 1 / ((2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1))

theorem psiCoeff_pos (k : ℕ) : 0 < psiCoeff k := by unfold psiCoeff; positivity

theorem psiCoeff_nonneg (k : ℕ) : 0 ≤ psiCoeff k := (psiCoeff_pos k).le

@[simp] theorem psiCoeff_zero : psiCoeff 0 = 1 / 2 := by norm_num [psiCoeff]

theorem hasSum_artanh {v : ℝ} (hv : |v| < 1) :
    HasSum (fun k : ℕ => v ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) (Real.artanh v) := by
  have h := (Real.hasSum_log_sub_log_of_abs_lt_one hv).mul_left (1 / 2)
  convert h using 1
  · ext k
    ring
  · rw [artanh_eq_log_sub (abs_lt.mp hv)]
    ring

theorem hasSum_mul_artanh {v : ℝ} (hv : |v| < 1) :
    HasSum (fun k : ℕ => (2 * ((k : ℝ) + 1)) * psiCoeff k * v ^ (2 * (k + 1)))
      (v * Real.artanh v) := by
  have h := (hasSum_artanh hv).mul_left v
  convert h using 1
  ext k
  have h1 : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
  have h2 : 2 * (k : ℝ) + 2 ≠ 0 := by positivity
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, pow_succ]
  unfold psiCoeff
  field_simp

theorem psi_eq_mul_artanh_add_log {v : ℝ} (hv : |v| < 1) :
    psi v = v * Real.artanh v + 1 / 2 * Real.log (1 - v ^ 2) := by
  have hp : 1 + v ≠ 0 := by linarith [(abs_lt.mp hv).1]
  have hm : 1 - v ≠ 0 := by linarith [(abs_lt.mp hv).2]
  have hl : Real.log (1 - v ^ 2) = Real.log (1 + v) + Real.log (1 - v) := by
    rw [← Real.log_mul hp hm]
    congr 1
    ring
  rw [artanh_eq_log_sub (abs_lt.mp hv), hl]
  unfold psi
  ring

theorem hasSum_psi {v : ℝ} (hv : |v| < 1) :
    HasSum (fun k : ℕ => psiCoeff k * v ^ (2 * (k + 1))) (psi v) := by
  have hv2 : |v ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg v)]
    have h1 : 0 < 1 + v := by linarith [(abs_lt.mp hv).1]
    have h2 : 0 < 1 - v := by linarith [(abs_lt.mp hv).2]
    nlinarith [mul_pos h1 h2]
  have h := ((hasSum_artanh hv).mul_left v).add
    ((Real.hasSum_pow_div_log_of_abs_lt_one hv2).mul_left (-(1 / 2)))
  convert h using 1
  · ext k
    have h1 : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (k : ℝ) + 1 ≠ 0 := by positivity
    have h3 : 2 * (k : ℝ) + 2 ≠ 0 := by positivity
    rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by omega, pow_succ]
    unfold psiCoeff
    field_simp
    ring
  · rw [psi_eq_mul_artanh_add_log hv]
    ring

theorem sum_range_artanh_le {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (m : ℕ) :
    (∑ k ∈ Finset.range m, v ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) ≤ Real.artanh v := by
  have h := hasSum_artanh (show |v| < 1 by rwa [abs_of_nonneg hv0])
  rw [← h.tsum_eq]
  exact h.summable.sum_le_tsum (Finset.range m) (fun k hk => by positivity)

theorem sum_range_psi_le {v : ℝ} (hv : |v| < 1) (m : ℕ) :
    (∑ k ∈ Finset.range m, psiCoeff k * v ^ (2 * (k + 1))) ≤ psi v := by
  have h := hasSum_psi hv
  rw [← h.tsum_eq]
  exact h.summable.sum_le_tsum (Finset.range m) (fun k hk =>
    mul_nonneg (psiCoeff_nonneg k) (Even.pow_nonneg (even_two_mul (k + 1)) v))

theorem summable_psiCoeff : Summable psiCoeff := by
  have h : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  apply Summable.of_nonneg_of_le psiCoeff_nonneg ?_ h
  intro k
  unfold psiCoeff
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [sq_nonneg (k : ℝ), Nat.cast_nonneg (α := ℝ) k]

end LeanBlast.CourtadeKumar

end

end OAI
