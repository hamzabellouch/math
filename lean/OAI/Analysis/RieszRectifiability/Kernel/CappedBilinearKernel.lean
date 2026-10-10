import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.FarKernelDifference
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalBilinear
import OAI.Analysis.RieszRectifiability.Kernel.LipschitzTests

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set Function
open scoped NNReal

def cappedInverseDistancePow {X : Type*} [PseudoMetricSpace X]
    (m : ℕ) (ε : ℝ) (q : X × X) : ℝ :=
  ((max ε (dist q.1 q.2)) ^ m)⁻¹

theorem cappedInverseDistancePow_nonneg {X : Type*} [PseudoMetricSpace X]
    (m : ℕ) (ε : ℝ) (q : X × X) : 0 ≤ cappedInverseDistancePow m ε q := by
  unfold cappedInverseDistancePow
  exact inv_nonneg.mpr (pow_nonneg (le_trans dist_nonneg (le_max_right _ _)) _)

theorem cappedInverseDistancePow_bound {X : Type*} [PseudoMetricSpace X]
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) (q : X × X) :
    |cappedInverseDistancePow m ε q| ≤ (ε ^ m)⁻¹ := by
  rw [abs_of_nonneg (cappedInverseDistancePow_nonneg m ε q)]
  unfold cappedInverseDistancePow
  exact inv_anti₀ (pow_pos hε _) (pow_le_pow_left₀ hε.le (le_max_left _ _) _)

theorem cappedInverseDistancePow_eq {X : Type*} [PseudoMetricSpace X]
    (m : ℕ) (ε : ℝ) (q : X × X) (h : ε ≤ dist q.1 q.2) :
    cappedInverseDistancePow m ε q = (dist q.1 q.2 ^ m)⁻¹ := by
  simp only [cappedInverseDistancePow, max_eq_right h]

theorem cappedInverseDistancePow_swap {X : Type*} [PseudoMetricSpace X]
    (m : ℕ) (ε : ℝ) (q : X × X) :
    cappedInverseDistancePow m ε q.swap = cappedInverseDistancePow m ε q := by
  simp only [cappedInverseDistancePow, Prod.swap, dist_comm]

theorem cappedInverseDistancePow_lipschitz {X : Type*} [PseudoMetricSpace X]
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    LipschitzWith (Real.toNNReal (2 * (m + 1 : ℝ) * (ε ^ (m + 2))⁻¹))
      (cappedInverseDistancePow (m + 1) ε : X × X → ℝ) := by
  have hmax : LipschitzWith 2 (fun q : X × X => max ε (dist q.1 q.2)) :=
    LipschitzWith.dist.const_max ε
  apply LipschitzWith.of_dist_le_mul
  intro q r
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity : 0 ≤ 2 * (m + 1 : ℝ) * (ε ^ (m + 2))⁻¹)]
  have hd : |max ε (dist q.1 q.2) - max ε (dist r.1 r.2)| ≤ 2 * dist q r := by
    simpa only [Real.dist_eq, NNReal.coe_ofNat] using! hmax.dist_le_mul q r
  calc
    _ ≤ (m + 1 : ℝ) * |max ε (dist q.1 q.2) - max ε (dist r.1 r.2)| * (ε ^ (m + 2))⁻¹ :=
      inverse_pow_difference_le m _ _ ε hε (le_max_left _ _) (le_max_left _ _)
    _ ≤ (m + 1 : ℝ) * (2 * dist q r) * (ε ^ (m + 2))⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by positivity)) (by positivity)
    _ = _ := by ring

def cappedTestKernel {d : ℕ} (m : ℕ) (ε : ℝ) (φ : Ambient d → ℝ)
    (q : Ambient d × Ambient d) : ℝ :=
  (φ q.1 - φ q.2) * cappedInverseDistancePow (m + 1) ε q

theorem cappedTestKernel_bound {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (φ : Ambient d → ℝ) (B : ℝ≥0) (hB : ∀ x, |φ x| ≤ (B : ℝ))
    (q : Ambient d × Ambient d) :
    |cappedTestKernel m ε φ q| ≤ (2 * (B : ℝ)) * (ε ^ (m + 1))⁻¹ := by
  unfold cappedTestKernel
  rw [abs_mul]
  have hd : |φ q.1 - φ q.2| ≤ 2 * (B : ℝ) := by
    have h := abs_sub_le (φ q.1) 0 (φ q.2)
    simp only [sub_zero, zero_sub, abs_neg] at h
    linarith [hB q.1, hB q.2]
  exact mul_le_mul hd (cappedInverseDistancePow_bound (m + 1) ε hε q) (abs_nonneg _) (by positivity)

theorem cappedTestKernel_lipschitz {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (φ : Ambient d → ℝ) (L B : ℝ≥0) (hφ : LipschitzWith L φ) (hB : ∀ x, |φ x| ≤ (B : ℝ)) :
    LipschitzWith
      ((2 * B) * Real.toNNReal (2 * (m + 1 : ℝ) * (ε ^ (m + 2))⁻¹) +
        (L + L) * Real.toNNReal ((ε ^ (m + 1))⁻¹)) (cappedTestKernel m ε φ) := by
  have hdiff : LipschitzWith (L + L) (fun q : Ambient d × Ambient d => φ q.1 - φ q.2) := by
    simpa only [mul_one] using! (hφ.comp LipschitzWith.prod_fst).sub (hφ.comp LipschitzWith.prod_snd)
  apply lipschitz_bounded_product_real hdiff (cappedInverseDistancePow_lipschitz m ε hε)
  · intro q
    have h := abs_sub_le (φ q.1) 0 (φ q.2)
    simp only [sub_zero, zero_sub, abs_neg] at h
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    linarith [hB q.1, hB q.2]
  · intro q
    exact (cappedInverseDistancePow_bound (m + 1) ε hε q).trans (Real.le_coe_toNNReal _)

theorem cappedTestKernel_antisymm {d : ℕ} (m : ℕ) (ε : ℝ) (φ : Ambient d → ℝ)
    (q : Ambient d × Ambient d) : cappedTestKernel m ε φ q.swap = -cappedTestKernel m ε φ q := by
  unfold cappedTestKernel
  rw [cappedInverseDistancePow_swap]
  dsimp only [Prod.swap]
  ring

theorem capped_bilinear_eq_outside {d : ℕ} (m : ℕ) (ε : ℝ) (w φ : Ambient d → ℝ)
    (q : Ambient d × Ambient d) (h : ε ≤ dist q.1 q.2) :
    (w q.1 - w q.2) * cappedTestKernel m ε φ q = fractionalBilinear m w φ q.1 q.2 := by
  unfold cappedTestKernel fractionalBilinear
  rw [cappedInverseDistancePow_eq _ _ _ h]
  ring

end

end RieszRectifiability

end OAI
