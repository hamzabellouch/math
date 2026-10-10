import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.L2Pairings

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function
open scoped NNReal

variable {d : ℕ}

def fractionalBilinear (m : ℕ) (w ψ : Ambient d → ℝ) (x y : Ambient d) : ℝ :=
  ((w x - w y) * (ψ x - ψ y)) / dist x y ^ (m + 1)

def weightedDifference (m : ℕ) (w : Ambient d → ℝ) (x y : Ambient d) : ℝ :=
  (w x - w y) / Real.sqrt (dist x y ^ (m + 1))

theorem weightedDifference_measurable (m : ℕ) (w : Ambient d → ℝ) (hw : Measurable w) :
    Measurable (fun q : Ambient d × Ambient d => weightedDifference m w q.1 q.2) := by
  unfold weightedDifference
  fun_prop

theorem weightedDifference_sq (m : ℕ) (w : Ambient d → ℝ) (x y : Ambient d) :
    weightedDifference m w x y ^ 2 = fractionalPairEnergy m w x y := by
  rw [weightedDifference, div_pow, Real.sq_sqrt (pow_nonneg dist_nonneg _)]
  rfl

theorem weightedDifference_mul (m : ℕ) (w ψ : Ambient d → ℝ) (x y : Ambient d) :
    weightedDifference m w x y * weightedDifference m ψ x y = fractionalBilinear m w ψ x y := by
  rw [weightedDifference, weightedDifference, div_mul_div_comm, ← pow_two,
    Real.sq_sqrt (pow_nonneg dist_nonneg _)]
  rfl

theorem lipschitz_fractionalEnergy_bound (p : ℕ) (ψ : Ambient d → ℝ)
    (L : ℝ≥0) (hψ : LipschitzWith L ψ) (x y : Ambient d) :
    fractionalPairEnergy (p + 1) ψ x y ≤ (L : ℝ) ^ 2 * (dist x y ^ p)⁻¹ := by
  by_cases hxy : x = y
  · subst y
    simp only [fractionalPairEnergy, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div]
    positivity
  · have hd : 0 < dist x y := dist_pos.mpr hxy
    have hdiff : |ψ x - ψ y| ≤ (L : ℝ) * dist x y := by
      simpa only [Real.dist_eq] using! hψ.dist_le_mul x y
    have hsq : (ψ x - ψ y) ^ 2 ≤ (L : ℝ) ^ 2 * dist x y ^ 2 := by
      simpa only [sq_abs, mul_pow] using!
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg L.coe_nonneg dist_nonneg)).mpr hdiff
    calc
      _ ≤ ((L : ℝ) ^ 2 * dist x y ^ 2) / dist x y ^ (p + 1 + 1) :=
        div_le_div_of_nonneg_right hsq (pow_nonneg dist_nonneg _)
      _ = _ := by
        rw [show p + 1 + 1 = p + 2 by omega, pow_add]
        field_simp

theorem weightedDifference_memLp (m : ℕ) (w : Ambient d → ℝ) (hw : Measurable w)
    (ρ : Measure (Ambient d × Ambient d))
    (hE : Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy m w q.1 q.2) ρ) :
    MemLp (fun q : Ambient d × Ambient d => weightedDifference m w q.1 q.2) 2 ρ := by
  apply (memLp_two_iff_integrable_sq (weightedDifference_measurable m w hw).aestronglyMeasurable).mpr
  simpa only [weightedDifference_sq] using! hE

end

end RieszRectifiability

end OAI
