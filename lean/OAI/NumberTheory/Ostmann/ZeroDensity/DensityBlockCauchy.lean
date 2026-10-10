import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFiniteContinuity

namespace OAI

/-! # Combining the finite coefficient blocks without a length loss -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Classical

 theorem density_weighted_sum_norm_sq {ι : Type*} (S : Finset ι)
    (f : ι → ℂ) (w : ι → ℝ) (hw : ∀ i ∈ S, 0 < w i) :
    ‖∑ i ∈ S, f i‖ ^ 2 ≤ (∑ i ∈ S, w i) * ∑ i ∈ S, ‖f i‖ ^ 2 / w i := by
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (fun i hi => (hw i hi).le) (fun i hi => div_nonneg (sq_nonneg _) (hw i hi).le)
  intro i hi
  rw [mul_div_cancel₀ _ (hw i hi).ne']

 theorem density_weighted_block_mean {α ι : Type*} (F : Finset α) (S : Finset ι)
    (f : α → ι → ℝ → ℂ) (w : ι → ℝ) (hw : ∀ i ∈ S, 0 < w i) (T : ℝ)
    (hf : ∀ χ ∈ F, ∀ i ∈ S, ContinuousOn (f χ i) (Icc (-T) T)) :
    (∑ χ ∈ F, ∫ t in Icc (-T) T, ‖∑ i ∈ S, f χ i t‖ ^ 2) ≤
      (∑ i ∈ S, w i) * ∑ i ∈ S,
        (∑ χ ∈ F, ∫ t in Icc (-T) T, ‖f χ i t‖ ^ 2) / w i := by
  have hi (χ : α) (hχ : χ ∈ F) (i : ι) (hi : i ∈ S) :
      Integrable (fun t => ‖f χ i t‖ ^ 2 / w i) (volume.restrict (Icc (-T) T)) :=
    (((hf χ hχ i hi).norm.pow 2).div_const _).integrableOn_Icc
  calc
    _ ≤ ∑ χ ∈ F, ∫ t in Icc (-T) T,
        (∑ i ∈ S, w i) * ∑ i ∈ S, ‖f χ i t‖ ^ 2 / w i := by
      apply Finset.sum_le_sum
      intro χ hχ
      apply integral_mono
      · exact ((continuousOn_finsetSum S (fun i hi => hf χ hχ i hi)).norm.pow 2).integrableOn_Icc
      · exact (integrable_finsetSum S (fun i hi' => hi χ hχ i hi')).const_mul _
      · intro t
        exact density_weighted_sum_norm_sq S (fun i => f χ i t) w hw
    _ = _ := by
      simp_rw [integral_const_mul]
      rw [← Finset.mul_sum]
      congr 1
      calc
        _ = ∑ χ ∈ F, ∑ i ∈ S, ∫ t in Icc (-T) T, ‖f χ i t‖ ^ 2 / w i := by
          apply Finset.sum_congr rfl
          intro χ hχ
          exact integral_finsetSum S (fun i hi' => hi χ hχ i hi')
        _ = _ := by
          rw [Finset.sum_comm]
          simp only [integral_div, Finset.sum_div]

end Ostmann

end OAI
