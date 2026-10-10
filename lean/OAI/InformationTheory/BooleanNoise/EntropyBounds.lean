import OAI.InformationTheory.BooleanNoise.EntropySeries
import Mathlib.Analysis.Normed.Group.FunctionSeries

namespace OAI

noncomputable section

open Set Filter Finset
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

def psiSeries (v : ℝ) : ℝ := ∑' k : ℕ, psiCoeff k * v ^ (2 * (k + 1))

theorem norm_psiSeries_term_le {v : ℝ} (hv : |v| ≤ 1) (k : ℕ) :
    ‖psiCoeff k * v ^ (2 * (k + 1))‖ ≤ psiCoeff k := by
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (psiCoeff_nonneg k)]
  exact mul_le_of_le_one_right (psiCoeff_nonneg k)
    (pow_le_one₀ (abs_nonneg v) hv)

theorem summable_psi_closed {v : ℝ} (hv : |v| ≤ 1) :
    Summable (fun k : ℕ => psiCoeff k * v ^ (2 * (k + 1))) :=
  Summable.of_norm_bounded summable_psiCoeff (norm_psiSeries_term_le hv)

theorem continuousOn_psiSeries : ContinuousOn psiSeries (Icc (-1) 1) := by
  apply continuousOn_tsum
  · intro k
    fun_prop
  · exact summable_psiCoeff
  · intro k v hv
    exact norm_psiSeries_term_le (abs_le.mpr hv) k

theorem psiSeries_eq_psi {v : ℝ} (hv : |v| ≤ 1) : psiSeries v = psi v := by
  have h : EqOn psiSeries psi (Ioo (-1) 1) := by
    intro x hx
    exact (hasSum_psi (abs_lt.mpr hx)).tsum_eq
  have h' := h.of_subset_closure continuousOn_psiSeries continuous_psi.continuousOn
    Ioo_subset_Icc_self (show Icc (-1 : ℝ) 1 ⊆ closure (Ioo (-1) 1) by
      rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)])
  exact h' (abs_le.mp hv)

theorem hasSum_psi_closed {v : ℝ} (hv : |v| ≤ 1) :
    HasSum (fun k : ℕ => psiCoeff k * v ^ (2 * (k + 1))) (psi v) := by
  rw [← psiSeries_eq_psi hv]
  exact (summable_psi_closed hv).hasSum

theorem hasSum_psiCoeff : HasSum psiCoeff ell := by
  simpa using hasSum_psi_closed (v := 1) (by norm_num)

theorem tsum_psiCoeff : ∑' k : ℕ, psiCoeff k = ell := hasSum_psiCoeff.tsum_eq

theorem half_sq_le_psi {v : ℝ} (hv : |v| ≤ 1) : v ^ 2 / 2 ≤ psi v := by
  have h := (summable_psi_closed hv).sum_le_tsum {0} (fun k hk =>
    mul_nonneg (psiCoeff_nonneg k) (Even.pow_nonneg (even_two_mul (k + 1)) v))
  rw [(hasSum_psi_closed hv).tsum_eq] at h
  simpa [psiCoeff_zero, div_eq_mul_inv, mul_comm] using h

theorem psi_le_ell_mul_sq {v : ℝ} (hv : |v| ≤ 1) : psi v ≤ ell * v ^ 2 := by
  have hsq : v ^ 2 ≤ 1 := by
    have h := abs_le.mp hv
    nlinarith [mul_nonneg (sub_nonneg.mpr h.2) (show 0 ≤ 1 + v by linarith [h.1])]
  apply hasSum_le _ (hasSum_psi_closed hv) (hasSum_psiCoeff.mul_right (v ^ 2))
  intro k
  apply mul_le_mul_of_nonneg_left _ (psiCoeff_nonneg k)
  rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add, pow_mul]
  exact mul_le_of_le_one_left (sq_nonneg v) (pow_le_one₀ (sq_nonneg v) hsq)

theorem ell_mul_one_sub_sq_le_entropy {v : ℝ} (hv : |v| ≤ 1) :
    ell * (1 - v ^ 2) ≤ entropy v := by
  have h := psi_le_ell_mul_sq hv
  unfold entropy
  nlinarith

end LeanBlast.CourtadeKumar

end

end OAI
