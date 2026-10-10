import OAI.Analysis.LipschitzHilbert.Fourier.PositiveConvolution

namespace OAI

/-! Short-scale convolution control by the sum of the actual source
functions before integration. This avoids a factor counting the scales. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem short_positiveConvolution_integral {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (len : ι → ℝ) (hlen : ∀ j, 0 < len j)
    (hf : ∀ j, Measurable (f j)) (hf0 : ∀ j s, 0 ≤ f j s)
    {M : ℝ} (hM : 0 ≤ M) (hsum : ∀ s, ∑ j, f j s ≤ M)
    (u r : ℝ) (hr : 0 < r) :
    (∫ x in Icc (u-r) (u+r),
      ∑ j, if len j ≤ r then positiveConvolution (len j) (f j) x else 0) ≤
      (1024 * Real.pi ^ 2) * M * r := by
  have hbound (j : ι) (s : ℝ) : f j s ≤ M :=
    (Finset.single_le_sum (fun i _ => hf0 i s) (Finset.mem_univ j)).trans (hsum s)
  let H := fun j s => if len j ≤ r then
    f j s * (∫ x in Icc (u-r) (u+r), lineKernel (len j) (x-s)) else 0
  have hH (j : ι) : Integrable (H j) := by
    by_cases hj : len j ≤ r
    · have hi := (positiveConvolution_joint_integrable (hf j) hM (hlen j) hr hj (hf0 j) (hbound j) u).integral_prod_left
      apply hi.congr
      filter_upwards [] with s
      change (∫ x in Icc (u-r) (u+r), lineKernel (len j) (x-s) * f j s) = H j s
      dsimp only [H]
      rw [ite_eq_left hj, integral_mul_const, mul_comm]
    · simp only [H, ite_eq_right hj]
      exact integrable_zero _ _ _
  have hG (j : ι) : IntegrableOn
      (fun x => if len j ≤ r then positiveConvolution (len j) (f j) x else 0) (Icc (u-r) (u+r)) := by
    by_cases hj : len j ≤ r
    · simpa only [ite_eq_left hj] using
        positiveConvolution_interval_integrable (hf j) hM (hlen j) hr hj (hf0 j) (hbound j) u
    · simp only [ite_eq_right hj]
      exact integrable_zero _ _ _
  have heq (j : ι) : (∫ x in Icc (u-r) (u+r),
      if len j ≤ r then positiveConvolution (len j) (f j) x else 0) = ∫ s, H j s := by
    by_cases hj : len j ≤ r
    · simp only [ite_eq_left hj, H]
      exact integral_positiveConvolution_interval (hf j) hM (hlen j) hr hj (hf0 j) (hbound j) u
    · simp only [ite_eq_right hj, H, integral_zero]
  have hpoint (s : ℝ) : (∑ j, H j s) ≤
      ((1024 * Real.pi) * M) * lineEnvelope u r 2 s := by
    have hpart : (∑ j, if len j ≤ r then f j s else 0) ≤ M := by
      apply le_trans _ (hsum s)
      apply Finset.sum_le_sum
      intro j _
      split_ifs <;> simp only [le_refl, hf0]
    calc
      _ ≤ ∑ j, ((1024 * Real.pi) * lineEnvelope u r 2 s) *
          (if len j ≤ r then f j s else 0) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : len j ≤ r
        · simp only [H, ite_eq_left hj]
          exact (mul_le_mul_of_nonneg_left
            (local_lineKernel_integral (len j) u r s (hlen j) hr hj) (hf0 j s)).trans_eq (mul_comm _ _)
        · simp only [H, ite_eq_right hj, mul_zero, le_refl]
      _ = ((1024 * Real.pi) * lineEnvelope u r 2 s) *
          ∑ j, if len j ≤ r then f j s else 0 := by rw [Finset.mul_sum]
      _ ≤ ((1024 * Real.pi) * lineEnvelope u r 2 s) * M :=
        mul_le_mul_of_nonneg_left hpart (mul_nonneg (by positivity) (lineEnvelope_nonneg _ _ _ _))
      _ = _ := by ring
  rw [integral_finsetSum _ (fun j _ => hG j)]
  simp_rw [heq]
  rw [← integral_finsetSum _ (fun j _ => hH j)]
  calc
    _ ≤ ∫ s, ((1024 * Real.pi) * M) * lineEnvelope u r 2 s :=
      integral_mono (integrable_finsetSum _ (fun j _ => hH j))
        ((integrable_lineEnvelope u r hr (by decide : 1 ≤ 2)).const_mul _) hpoint
    _ = ((1024 * Real.pi) * M) * ∫ s, lineEnvelope u r 2 s := integral_const_mul _ _
    _ ≤ ((1024 * Real.pi) * M) * (Real.pi*r) :=
      mul_le_mul_of_nonneg_left (integral_lineEnvelope_le u r hr (by decide : 1 ≤ 2)) (by positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
