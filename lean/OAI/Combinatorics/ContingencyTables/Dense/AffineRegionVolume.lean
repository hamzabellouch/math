import OAI.Combinatorics.ContingencyTables.Dense.AffineRegion
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

/-! # Volume comparisons used by dense rejection -/

namespace ContingencyTables.AffinePenalty

open MeasureTheory
open scoped BigOperators Pointwise

noncomputable section

variable {I G : Type*} [Fintype I]

theorem inner_region_volume (offset : G → ℝ) (coeff : G → I → ℝ)
    (center : I → ℝ) (η α : ℝ) (hα : 0 ≤ α) (hα₁ : α ≤ 1)
    (hc : center ∈ region offset coeff η) :
    ENNReal.ofReal ((1 - α) ^ Fintype.card I) * volume (region offset coeff 0) ≤
      volume (region offset coeff (α * η)) := by
  rw [← volume_homothety center (1 - α) (sub_nonneg.mpr hα₁)]
  have heq : (fun x : I → ℝ => center + (1 - α) • (x - center)) =
      (fun x => (1 - α) • x + α • center) := by
    ext x i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  exact measure_mono (inner_region_map offset coeff center η α hα hα₁ hc)

theorem relaxed_region_volume_exp (offset : G → ℝ) (coeff : G → I → ℝ)
    (center : I → ℝ) (d γ : ℝ) (hd : 0 < d) (hγ : 0 ≤ γ)
    (hdim : (Fintype.card I : ℝ) ≤ d)
    (hc : center ∈ region offset coeff (1 / (2 * d))) :
    volume (region offset coeff (-γ)) ≤
      ENNReal.ofReal (Real.exp (2 * d ^ 2 * γ)) * volume (region offset coeff 0) := by
  have hpoly : (1 + 2 * d * γ) ^ Fintype.card I ≤ Real.exp (2 * d ^ 2 * γ) := by
    calc
      _ ≤ (Real.exp (2 * d * γ)) ^ Fintype.card I :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (2 * d * γ)]) _
      _ = Real.exp ((Fintype.card I : ℝ) * (2 * d * γ)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have h := mul_le_mul_of_nonneg_right hdim (show 0 ≤ 2 * d * γ by positivity)
        nlinarith)
  exact (relaxed_region_volume offset coeff center d γ hd hγ hc).trans
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal hpoly) _)

end

end ContingencyTables.AffinePenalty

end OAI
