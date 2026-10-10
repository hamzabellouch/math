import Mathlib
import OAI.Probability.SKBarriers.Coverage.FiniteRate

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem quenchedPressure_quantitative_finiteInf {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      finiteParisiInf β-C*(N:ℝ)^(-(1:ℝ)/24) ≤ quenchedPressure β N ∧
      quenchedPressure β N ≤ finiteParisiInf β := by
  refine ⟨finiteRateConstant β,finiteRateConstant_pos hβ,?_⟩
  let r := fun N : ℕ => (N:ℝ)^((1:ℝ)/12)
  have HR : Tendsto r atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/12)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [HR.eventually (eventually_ge_atTop (2:ℝ)),eventually_gt_atTop (0:ℕ)] with N hr hN
  let k : ℕ := ⌈r N⌉₊
  have hr0 : 0 < r N := by linarith
  have hk0 : r N ≤ (k:ℝ) := Nat.le_ceil _
  have hk1 : (k:ℝ) ≤ 2*r N := by
    have H := Nat.ceil_lt_add_one hr0.le
    change (k:ℝ) < r N+1 at H
    linarith
  have hk : 0 < k := by exact_mod_cast (hr0.trans_le hk0)
  have hp : (N:ℝ) = (r N)^12 := by
    dsimp only [r]
    rw [← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  have hη : 0 < 1/(β^2*(r N)^4) := by positivity
  obtain ⟨hsmall,herr⟩ := finiteComparisonError_rate hβ hr hp hk0 hk1
  have HC := finiteParisiInf_sub_error_le hN hk hβ hη hsmall
  have hsqrt : Real.sqrt (r N) = (N:ℝ)^((1:ℝ)/24) := by
    rw [Real.sqrt_eq_rpow]
    dsimp only [r]
    rw [← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  have he : 1/Real.sqrt (r N) = (N:ℝ)^(-(1:ℝ)/24) := by
    rw [hsqrt,show -(1:ℝ)/24 = -(1/24) by ring,Real.rpow_neg (Nat.cast_nonneg N)]
    simp only [one_div]
  rw [he] at herr
  exact ⟨(sub_le_sub_left herr _).trans HC,quenched_le_finiteParisiInf hN β⟩
end SK.Analytic

end
end

end

end OAI
