import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.LocalizedRieszPairingBounds
import OAI.Analysis.RieszRectifiability.Kernel.CappedBilinearError

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

def cappedRieszInterior {d : ℕ} (m : ℕ) (ε : ℝ) (e : Ambient d)
    (φ : Ambient d → ℝ) (q : Ambient d × Ambient d) : ℝ :=
  inner ℝ e (q.1 - q.2) * (φ q.1 - φ q.2) * cappedInverseDistancePow (m + 1) ε q

theorem cappedRieszInterior_continuous {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (e : Ambient d) (φ : Ambient d → ℝ) (hφ : Continuous φ) :
    Continuous (cappedRieszInterior m ε e φ) := by
  have hc := (cappedInverseDistancePow_lipschitz (X := Ambient d) m ε hε).continuous
  unfold cappedRieszInterior
  fun_prop

theorem distance_mul_cappedInverseDistancePow_bound {X : Type*} [PseudoMetricSpace X]
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) (q : X × X) :
    dist q.1 q.2 * cappedInverseDistancePow (m + 1) ε q ≤ (ε ^ m)⁻¹ := by
  have hmax : 0 < max ε (dist q.1 q.2) := hε.trans_le (le_max_left _ _)
  calc
    _ ≤ max ε (dist q.1 q.2) * cappedInverseDistancePow (m + 1) ε q :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (cappedInverseDistancePow_nonneg _ _ _)
    _ = ((max ε (dist q.1 q.2)) ^ m)⁻¹ := by
      unfold cappedInverseDistancePow
      rw [pow_succ]
      field_simp
    _ ≤ _ := inv_anti₀ (pow_pos hε m) (pow_le_pow_left₀ hε.le (le_max_left _ _) m)

theorem cappedRieszInterior_bound {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (e : Ambient d) (φ : Ambient d → ℝ) (B : ℝ≥0)
    (hB : ∀ x, |φ x| ≤ (B : ℝ)) (q : Ambient d × Ambient d) :
    |cappedRieszInterior m ε e φ q| ≤ (2 * (B : ℝ) * ‖e‖) * (ε ^ m)⁻¹ := by
  have hi : |inner ℝ e (q.1 - q.2)| ≤ ‖e‖ * dist q.1 q.2 := by
    simpa only [Real.norm_eq_abs, dist_eq_norm] using!
      norm_inner_le_norm (𝕜 := ℝ) e (q.1 - q.2)
  have hd : |φ q.1 - φ q.2| ≤ 2 * (B : ℝ) := by
    have ht := abs_sub_le (φ q.1) 0 (φ q.2)
    simp only [sub_zero, zero_sub, abs_neg] at ht
    linarith [hB q.1, hB q.2]
  calc
    _ = |inner ℝ e (q.1 - q.2)| * |φ q.1 - φ q.2| *
        cappedInverseDistancePow (m + 1) ε q := by
      rw [cappedRieszInterior, abs_mul, abs_mul,
        abs_of_nonneg (cappedInverseDistancePow_nonneg _ _ _)]
    _ ≤ (‖e‖ * dist q.1 q.2) * (2 * (B : ℝ)) *
        cappedInverseDistancePow (m + 1) ε q :=
      mul_le_mul_of_nonneg_right (mul_le_mul hi hd (abs_nonneg _) (by positivity))
        (cappedInverseDistancePow_nonneg _ _ _)
    _ = (2 * (B : ℝ) * ‖e‖) *
        (dist q.1 q.2 * cappedInverseDistancePow (m + 1) ε q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (distance_mul_cappedInverseDistancePow_bound m ε hε q) (by positivity)

theorem cappedRieszInterior_eq_affine_bilinear {d : ℕ} (m : ℕ) (ε : ℝ)
    (e : Ambient d) (φ : Ambient d → ℝ) (q : Ambient d × Ambient d) :
    cappedRieszInterior m ε e φ q =
      (affineNormalHeight e 0 0 q.1 - affineNormalHeight e 0 0 q.2) *
        cappedTestKernel m ε φ q := by
  rw [affineNormalHeight_difference]
  unfold cappedRieszInterior cappedTestKernel
  ring

theorem rieszInterior_cap_error_pointwise {d : ℕ} (p : ℕ) (ε : ℝ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (q : Ambient d × Ambient d) :
    |rieszInteriorIntegrand (p + 1) e φ q - cappedRieszInterior (p + 1) ε e φ q| ≤
      (‖e‖ * (L : ℝ)) * nearPairWeight p ε q := by
  have hb := capped_bilinear_error_pointwise (p + 1) ε (affineNormalHeight e 0 0) φ q
  rw [← cappedRieszInterior_eq_affine_bilinear] at hb
  have heq := rieszInteriorIntegrand_eq_fractionalBilinear (p + 1) e
    (affineNormalHeight e 0 0) φ (affineNormalHeight_difference e 0 0)
  simp only [← heq] at hb
  apply hb.trans
  by_cases hq : q ∈ nearPairSet ε
  · rw [indicator_of_mem hq, nearPairWeight, indicator_of_mem hq]
    exact rieszInteriorIntegrand_weak_kernel_bound p e φ L hφ q.1 q.2
  · rw [indicator_of_notMem hq, nearPairWeight, indicator_of_notMem hq, mul_zero]

end

end RieszRectifiability

end OAI
